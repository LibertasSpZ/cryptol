-- |
-- Module      :  Cryptol.ModuleSystem.Renamer
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# Language RecordWildCards #-}
module Cryptol.ModuleSystem.Renamer (
    NamingEnv(), shadowing
  , BindsNames(..), InModule(..)
  , shadowNames
  , Rename(..), runRenamer, RenameM()
  , RenamerError(..)
  , RenamerWarning(..)
  , renameVar
  , renameType
  , renameModule
  , RenamerInfo(..)
  ) where

import Data.List(find)
import qualified Data.Map.Strict as Map
import           MonadLib hiding (mapM, mapM_)

import Prelude ()
import Prelude.Compat

import Cryptol.ModuleSystem.Name
import Cryptol.ModuleSystem.NamingEnv
import Cryptol.ModuleSystem.Exports
import Cryptol.Parser.AST
import Cryptol.Parser.Selector(selName)
import Cryptol.Utils.Panic (panic)
import Cryptol.Utils.RecordMap

import Cryptol.ModuleSystem.Interface
import Cryptol.ModuleSystem.Renamer.Error
import Cryptol.ModuleSystem.Renamer.Monad





class Rename f where
  rename :: f PName -> RenameM (f Name)

-- | Returns:
--
--    * Interfaces for imported things,
--    * Things defines in the module
--    * Renamed module
renameModule :: Module PName -> RenameM (IfaceDecls,NamingEnv,Module Name)
renameModule m =
  do (ds,imps) <- mconcat <$> mapM (lookupImport . thing) (mImports m)
     defs <- liftSupply (defsWithModsOf m)
     let env = defNames defs
     -- XXX: NM open looping, etc
     decls' <- shadowNames imps $
               shadowNames' CheckOverlap env $
               traverse rename (mDecls m)
     let m1      = m { mDecls = decls' }
         exports = modExports m1
     mapM_ recordUse (exported NSType exports)
     return (ds,env,m1)

{-
openLoop used undef os env =
  case os of
    o : more ->
      case lookupNS NSModule o env of
        [] -> openLoop (o : undef) more env
        [n] ->
          case asOrigName n of
            Just og -> let
            Nothing -> panic "openLoop" [ "Non top-level module name" ]
-}


instance Rename TopDecl where
  rename td     = case td of
    Decl d      -> Decl      <$> traverse rename d
    DPrimType d -> DPrimType <$> traverse rename d
    TDNewtype n -> TDNewtype <$> traverse rename n
    Include n   -> return (Include n)
    DParameterFun f  -> DParameterFun  <$> rename f
    DParameterType f -> DParameterType <$> rename f

    DParameterConstraint d -> DParameterConstraint <$> mapM renameLocated d

renameLocated :: Rename f => Located (f PName) -> RenameM (Located (f Name))
renameLocated x =
  do y <- rename (thing x)
     return x { thing = y }

instance Rename PrimType where
  rename pt =
    do x <- rnLocated renameType (primTName pt)
       let (as,ps) = primTCts pt
       (_,cts) <- renameQual as ps $ \as' ps' -> pure (as',ps')
       pure pt { primTCts = cts, primTName = x }

instance Rename ParameterType where
  rename a =
    do n' <- rnLocated renameType (ptName a)
       return a { ptName = n' }

instance Rename ParameterFun where
  rename a =
    do n'   <- rnLocated renameVar (pfName a)
       sig' <- renameSchema (pfSchema a)
       return a { pfName = n', pfSchema = snd sig' }

rnLocated :: (a -> RenameM b) -> Located a -> RenameM (Located b)
rnLocated f loc = withLoc loc $
  do a' <- f (thing loc)
     return loc { thing = a' }

instance Rename Decl where
  rename d      = case d of
    DSignature ns sig -> DSignature    <$> traverse (rnLocated renameVar) ns
                                       <*> rename sig
    DPragma ns p      -> DPragma       <$> traverse (rnLocated renameVar) ns
                                       <*> pure p
    DBind b           -> DBind         <$> rename b

    -- XXX we probably shouldn't see these at this point...
    DPatBind pat e    -> do (pe,pat') <- renamePat pat
                            shadowNames pe (DPatBind pat' <$> rename e)

    DType syn         -> DType         <$> rename syn
    DProp syn         -> DProp         <$> rename syn
    DLocated d' r     -> withLoc r
                       $ DLocated      <$> rename d'  <*> pure r
    DFixity{}         -> panic "Renamer" ["Unexpected fixity declaration"
                                         , show d]

instance Rename Newtype where
  rename n      = do
    name' <- rnLocated renameType (nName n)
    shadowNames (nParams n) $
      do ps'   <- traverse rename (nParams n)
         body' <- traverse (traverse rename) (nBody n)
         return Newtype { nName   = name'
                        , nParams = ps'
                        , nBody   = body' }

renameVar :: PName -> RenameM Name
renameVar qn = do
  ro <- RenameM ask
  case Map.lookup qn (namespaceMap NSValue (roNames ro)) of
    Just [n]  -> return n
    Just []   -> panic "Renamer" ["Invalid expression renaming environment"]
    Just syms ->
      do n <- located qn
         record (MultipleSyms n syms)
         return (head syms)

    -- This is an unbound value. Record an error and invent a bogus real name
    -- for it.
    Nothing ->
      do n <- located qn

         case Map.lookup qn (namespaceMap NSType (roNames ro)) of
           -- types existed with the name of the value expected
           Just _ -> record (ExpectedValue n)

           -- the value is just missing
           Nothing -> record (UnboundExpr n)

         mkFakeName NSValue qn

-- | Produce a name if one exists. Note that this includes situations where
-- overlap exists, as it's just a query about anything being in scope. In the
-- event that overlap does exist, an error will be recorded.
typeExists :: PName -> RenameM (Maybe Name)
typeExists pn =
  do ro <- RenameM ask
     case Map.lookup pn (namespaceMap NSType (roNames ro)) of
       Just [n]  -> recordUse n >> return (Just n)
       Just []   -> panic "Renamer" ["Invalid type renaming environment"]
       Just syms -> do n <- located pn
                       mapM_ recordUse syms
                       record (MultipleSyms n syms)
                       return (Just (head syms))
       Nothing -> return Nothing

renameType :: PName -> RenameM Name
renameType pn =
  do mb <- typeExists pn
     case mb of
       Just n -> return n

       -- This is an unbound value. Record an error and invent a bogus real name
       -- for it.
       Nothing ->
         do ro <- RenameM ask
            let n = Located { srcRange = roLoc ro, thing = pn }

            case Map.lookup pn (namespaceMap NSValue (roNames ro)) of

              -- values exist with the same name, so throw a different error
              Just _ -> record (ExpectedType n)

              -- no terms with the same name, so the type is just unbound
              Nothing -> record (UnboundType n)

            mkFakeName NSType pn

-- | Assuming an error has been recorded already, construct a fake name that's
-- not expected to make it out of the renamer.
mkFakeName :: Namespace -> PName -> RenameM Name
mkFakeName ns pn =
  do ro <- RenameM ask
     liftSupply (mkParameter ns (getIdent pn) (roLoc ro))

-- | Rename a schema, assuming that none of its type variables are already in
-- scope.
instance Rename Schema where
  rename s = snd `fmap` renameSchema s

-- | Rename a schema, assuming that the type variables have already been brought
-- into scope.
renameSchema :: Schema PName -> RenameM (NamingEnv,Schema Name)
renameSchema (Forall ps p ty loc) =
  renameQual ps p $ \ps' p' ->
    do ty' <- rename ty
       pure (Forall ps' p' ty' loc)

-- | Rename a qualified thing.
renameQual :: [TParam PName] -> [Prop PName] ->
              ([TParam Name] -> [Prop Name] -> RenameM a) ->
              RenameM (NamingEnv, a)
renameQual as ps k =
  do env <- liftSupply (namingEnv' as)
     res <- shadowNames env $ do as' <- traverse rename as
                                 ps' <- traverse rename ps
                                 k as' ps'
     pure (env,res)

instance Rename TParam where
  rename TParam { .. } =
    do n <- renameType tpName
       return TParam { tpName = n, .. }

instance Rename Prop where
  rename (CType t) = CType <$> rename t


instance Rename Type where
  rename ty0 =
    case ty0 of
      TFun a b       -> TFun <$> rename a <*> rename b
      TSeq n a       -> TSeq <$> rename n <*> rename a
      TBit           -> return TBit
      TNum c         -> return (TNum c)
      TChar c        -> return (TChar c)
      TUser qn ps    -> TUser    <$> renameType qn <*> traverse rename ps
      TTyApp fs      -> TTyApp   <$> traverse (traverse rename) fs
      TRecord fs     -> TRecord  <$> traverse (traverse rename) fs
      TTuple fs      -> TTuple   <$> traverse rename fs
      TWild          -> return TWild
      TLocated t' r  -> withLoc r (TLocated <$> rename t' <*> pure r)
      TParens t'     -> TParens <$> rename t'
      TInfix a o _ b -> do o' <- renameTypeOp o
                           a' <- rename a
                           b' <- rename b
                           mkTInfix a' o' b'

mkTInfix ::
  Type Name -> (Located Name, Fixity) -> Type Name -> RenameM (Type Name)

mkTInfix t@(TInfix x o1 f1 y) op@(o2,f2) z =
  case compareFixity f1 f2 of
    FCLeft  -> return (TInfix t o2 f2 z)
    FCRight -> do r <- mkTInfix y op z
                  return (TInfix x o1 f1 r)
    FCError -> do record (FixityError o1 f1 o2 f2)
                  return (TInfix t o2 f2 z)

mkTInfix (TLocated t' _) op z =
  mkTInfix t' op z

mkTInfix t (o,f) z =
  return (TInfix t o f z)


-- | Rename a binding.
instance Rename Bind where
  rename b      = do
    n'    <- rnLocated renameVar (bName b)
    mbSig <- traverse renameSchema (bSignature b)
    shadowNames (fst `fmap` mbSig) $
      do (patEnv,pats') <- renamePats (bParams b)
         -- NOTE: renamePats will generate warnings, so we don't need to trigger
         -- them again here.
         e'             <- shadowNames' CheckNone patEnv (rnLocated rename (bDef b))
         return b { bName      = n'
                  , bParams    = pats'
                  , bDef       = e'
                  , bSignature = snd `fmap` mbSig
                  , bPragmas   = bPragmas b
                  }

instance Rename BindDef where
  rename DPrim     = return DPrim
  rename (DExpr e) = DExpr <$> rename e

-- NOTE: this only renames types within the pattern.
instance Rename Pattern where
  rename p      = case p of
    PVar lv         -> PVar <$> rnLocated renameVar lv
    PWild           -> pure PWild
    PTuple ps       -> PTuple   <$> traverse rename ps
    PRecord nps     -> PRecord  <$> traverse (traverse rename) nps
    PList elems     -> PList    <$> traverse rename elems
    PTyped p' t     -> PTyped   <$> rename p'    <*> rename t
    PSplit l r      -> PSplit   <$> rename l     <*> rename r
    PLocated p' loc -> withLoc loc
                     $ PLocated <$> rename p'    <*> pure loc

-- | Note that after this point the @->@ updates have an explicit function
-- and there are no more nested updates.
instance Rename UpdField where
  rename (UpdField h ls e) =
    -- The plan:
    -- x =  e       ~~~>        x = e
    -- x -> e       ~~~>        x -> \x -> e
    -- x.y = e      ~~~>        x -> { _ | y = e }
    -- x.y -> e     ~~~>        x -> { _ | y -> e }
    case ls of
      l : more ->
       case more of
         [] -> case h of
                 UpdSet -> UpdField UpdSet [l] <$> rename e
                 UpdFun -> UpdField UpdFun [l] <$> rename (EFun [PVar p] e)
                       where
                       p = UnQual . selName <$> last ls
         _ -> UpdField UpdFun [l] <$> rename (EUpd Nothing [ UpdField h more e])
      [] -> panic "rename@UpdField" [ "Empty label list." ]


instance Rename Expr where
  rename expr = case expr of
    EVar n          -> EVar <$> renameVar n
    ELit l          -> return (ELit l)
    ENeg e          -> ENeg    <$> rename e
    EComplement e   -> EComplement
                               <$> rename e
    EGenerate e     -> EGenerate
                               <$> rename e
    ETuple es       -> ETuple  <$> traverse rename es
    ERecord fs      -> ERecord <$> traverse (traverse rename) fs
    ESel e' s       -> ESel    <$> rename e' <*> pure s
    EUpd mb fs      -> do checkLabels fs
                          EUpd <$> traverse rename mb <*> traverse rename fs
    EList es        -> EList   <$> traverse rename es
    EFromTo s n e t -> EFromTo <$> rename s
                               <*> traverse rename n
                               <*> rename e
                               <*> traverse rename t
    EInfFrom a b    -> EInfFrom<$> rename a  <*> traverse rename b
    EComp e' bs     -> do arms' <- traverse renameArm bs
                          let (envs,bs') = unzip arms'
                          -- NOTE: renameArm will generate shadowing warnings; we only
                          -- need to check for repeated names across multiple arms
                          shadowNames' CheckOverlap envs (EComp <$> rename e' <*> pure bs')
    EApp f x        -> EApp    <$> rename f  <*> rename x
    EAppT f ti      -> EAppT   <$> rename f  <*> traverse rename ti
    EIf b t f       -> EIf     <$> rename b  <*> rename t  <*> rename f
    EWhere e' ds    -> do ns <- getNS
                          shadowNames (map (InModule ns) ds) $
                            EWhere <$> rename e' <*> traverse rename ds
    ETyped e' ty    -> ETyped  <$> rename e' <*> rename ty
    ETypeVal ty     -> ETypeVal<$> rename ty
    EFun ps e'      -> do (env,ps') <- renamePats ps
                          -- NOTE: renamePats will generate warnings, so we don't
                          -- need to duplicate them here
                          shadowNames' CheckNone env (EFun ps' <$> rename e')
    ELocated e' r   -> withLoc r
                     $ ELocated <$> rename e' <*> pure r

    ESplit e        -> ESplit  <$> rename e
    EParens p       -> EParens <$> rename p
    EInfix x y _ z  -> do op <- renameOp y
                          x' <- rename x
                          z' <- rename z
                          mkEInfix x' op z'


checkLabels :: [UpdField PName] -> RenameM ()
checkLabels = foldM_ check [] . map labs
  where
  labs (UpdField _ ls _) = ls

  check done l =
    do case find (overlap l) done of
         Just l' -> record (OverlappingRecordUpdate (reLoc l) (reLoc l'))
         Nothing -> pure ()
       pure (l : done)

  overlap xs ys =
    case (xs,ys) of
      ([],_)  -> True
      (_, []) -> True
      (x : xs', y : ys') -> same x y && overlap xs' ys'

  same x y =
    case (thing x, thing y) of
      (TupleSel a _, TupleSel b _)   -> a == b
      (ListSel  a _, ListSel  b _)   -> a == b
      (RecordSel a _, RecordSel b _) -> a == b
      _                              -> False

  reLoc xs = (head xs) { thing = map thing xs }


mkEInfix :: Expr Name             -- ^ May contain infix expressions
         -> (Located Name,Fixity) -- ^ The operator to use
         -> Expr Name             -- ^ Will not contain infix expressions
         -> RenameM (Expr Name)

mkEInfix e@(EInfix x o1 f1 y) op@(o2,f2) z =
   case compareFixity f1 f2 of
     FCLeft  -> return (EInfix e o2 f2 z)

     FCRight -> do r <- mkEInfix y op z
                   return (EInfix x o1 f1 r)

     FCError -> do record (FixityError o1 f1 o2 f2)
                   return (EInfix e o2 f2 z)

mkEInfix (ELocated e' _) op z =
     mkEInfix e' op z

mkEInfix e (o,f) z =
     return (EInfix e o f z)


renameOp :: Located PName -> RenameM (Located Name, Fixity)
renameOp ln =
  withLoc ln $
  do n <- renameVar (thing ln)
     fixity <- lookupFixity n
     return (ln { thing = n }, fixity)

renameTypeOp :: Located PName -> RenameM (Located Name, Fixity)
renameTypeOp ln =
  withLoc ln $
  do n <- renameType (thing ln)
     fixity <- lookupFixity n
     return (ln { thing = n }, fixity)

lookupFixity :: Name -> RenameM Fixity
lookupFixity n =
  case nameFixity n of
    Just fixity -> return fixity
    Nothing     -> return defaultFixity -- FIXME: should we raise an error instead?

instance Rename TypeInst where
  rename ti = case ti of
    NamedInst nty -> NamedInst <$> traverse rename nty
    PosInst ty    -> PosInst   <$> rename ty

renameArm :: [Match PName] -> RenameM (NamingEnv,[Match Name])

renameArm (m:ms) =
  do (me,m') <- renameMatch m
     -- NOTE: renameMatch will generate warnings, so we don't
     -- need to duplicate them here
     shadowNames' CheckNone me $
       do (env,rest) <- renameArm ms

          -- NOTE: the inner environment shadows the outer one, for examples
          -- like this:
          --
          -- [ x | x <- xs, let x = 10 ]
          return (env `shadowing` me, m':rest)

renameArm [] =
     return (mempty,[])

-- | The name environment generated by a single match.
renameMatch :: Match PName -> RenameM (NamingEnv,Match Name)

renameMatch (Match p e) =
  do (pe,p') <- renamePat p
     e'      <- rename e
     return (pe,Match p' e')

renameMatch (MatchLet b) =
  do ns <- getNS
     be <- liftSupply (namingEnv' (InModule ns b))
     b' <- shadowNames be (rename b)
     return (be,MatchLet b')

-- | Rename patterns, and collect the new environment that they introduce.
renamePat :: Pattern PName -> RenameM (NamingEnv, Pattern Name)
renamePat p =
  do pe <- patternEnv p
     p' <- shadowNames pe (rename p)
     return (pe, p')



-- | Rename patterns, and collect the new environment that they introduce.
renamePats :: [Pattern PName] -> RenameM (NamingEnv,[Pattern Name])
renamePats  = loop
  where
  loop ps = case ps of

    p:rest -> do
      pe <- patternEnv p
      shadowNames pe $
        do p'           <- rename p
           (env',rest') <- loop rest
           return (pe `mappend` env', p':rest')

    [] -> return (mempty, [])

patternEnv :: Pattern PName -> RenameM NamingEnv
patternEnv  = go
  where
  go (PVar Located { .. }) =
    do n <- liftSupply (mkParameter NSValue (getIdent thing) srcRange)
       return (singletonE thing n)

  go PWild            = return mempty
  go (PTuple ps)      = bindVars ps
  go (PRecord fs)     = bindVars (fmap snd (recordElements fs))
  go (PList ps)       = foldMap go ps
  go (PTyped p ty)    = go p `mappend` typeEnv ty
  go (PSplit a b)     = go a `mappend` go b
  go (PLocated p loc) = withLoc loc (go p)

  bindVars []     = return mempty
  bindVars (p:ps) =
    do env <- go p
       shadowNames env $
         do rest <- bindVars ps
            return (env `mappend` rest)


  typeEnv (TFun a b) = bindTypes [a,b]
  typeEnv (TSeq a b) = bindTypes [a,b]

  typeEnv TBit       = return mempty
  typeEnv TNum{}     = return mempty
  typeEnv TChar{}    = return mempty

  typeEnv (TUser pn ps) =
    do mb <- typeExists pn
       case mb of

         -- The type is already bound, don't introduce anything.
         Just _ -> bindTypes ps

         Nothing

           -- The type isn't bound, and has no parameters, so it names a portion
           -- of the type of the pattern.
           | null ps ->
             do loc <- curLoc
                n   <- liftSupply (mkParameter NSType (getIdent pn) loc)
                return (singletonT pn n)

           -- This references a type synonym that's not in scope. Record an
           -- error and continue with a made up name.
           | otherwise ->
             do loc <- curLoc
                record (UnboundType (Located loc pn))
                n   <- liftSupply (mkParameter NSType (getIdent pn) loc)
                return (singletonT pn n)

  typeEnv (TRecord fs)      = bindTypes (map snd (recordElements fs))
  typeEnv (TTyApp fs)       = bindTypes (map value fs)
  typeEnv (TTuple ts)       = bindTypes ts
  typeEnv TWild             = return mempty
  typeEnv (TLocated ty loc) = withLoc loc (typeEnv ty)
  typeEnv (TParens ty)      = typeEnv ty
  typeEnv (TInfix a _ _ b)  = bindTypes [a,b]

  bindTypes [] = return mempty
  bindTypes (t:ts) =
    do env' <- typeEnv t
       shadowNames env' $
         do res <- bindTypes ts
            return (env' `mappend` res)


instance Rename Match where
  rename m = case m of
    Match p e  ->                  Match    <$> rename p <*> rename e
    MatchLet b -> shadowNamesNS b (MatchLet <$> rename b)

instance Rename TySyn where
  rename (TySyn n f ps ty) =
    shadowNames ps $ TySyn <$> rnLocated renameType n
                           <*> pure f
                           <*> traverse rename ps
                           <*> rename ty

instance Rename PropSyn where
  rename (PropSyn n f ps cs) =
    shadowNames ps $ PropSyn <$> rnLocated renameType n
                             <*> pure f
                             <*> traverse rename ps
                             <*> traverse rename cs

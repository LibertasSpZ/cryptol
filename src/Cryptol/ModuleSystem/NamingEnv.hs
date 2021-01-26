-- |
-- Module      :  Cryptol.ModuleSystem.NamingEnv
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RecordWildCards #-}
module Cryptol.ModuleSystem.NamingEnv where

import Data.List (nub)
import Data.Maybe (fromMaybe,mapMaybe)
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Set (Set)
import qualified Data.Set as Set
import Data.Semigroup
import MonadLib (runId,Id)

import GHC.Generics (Generic)
import Control.DeepSeq

import Prelude ()
import Prelude.Compat

import Cryptol.Utils.PP
import Cryptol.Utils.Panic (panic)
import Cryptol.Parser.AST
import Cryptol.Parser.Name(isGeneratedName)
import Cryptol.Parser.Position
import qualified Cryptol.TypeCheck.AST as T
import Cryptol.ModuleSystem.Interface
import Cryptol.ModuleSystem.Name


-- Naming Environment ----------------------------------------------------------

-- | The 'NamingEnv' is used by the renamer to determine what
-- identifiers refer to.
newtype NamingEnv = NamingEnv (Map Namespace (Map PName [Name]))
  deriving (Show,Generic,NFData)

-- | Get the names in a given namespace
namespaceMap :: Namespace -> NamingEnv -> Map PName [Name]
namespaceMap ns (NamingEnv env) = Map.findWithDefault Map.empty ns env

-- | Resolve a name in the given namespace.
lookupNS :: Namespace -> PName -> NamingEnv -> [Name]
lookupNS ns x = Map.findWithDefault [] x . namespaceMap ns

-- | Return a list of value-level names to which this parsed name may refer.
lookupValNames :: PName -> NamingEnv -> [Name]
lookupValNames = lookupNS NSValue

-- | Return a list of type-level names to which this parsed name may refer.
lookupTypeNames :: PName -> NamingEnv -> [Name]
lookupTypeNames = lookupNS NSType

-- | Singleton renaming environment for the given namespace.
singletonNS :: Namespace -> PName -> Name -> NamingEnv
singletonNS ns pn n = NamingEnv (Map.singleton ns (Map.singleton pn [n]))

-- | Singleton expression renaming environment.
singletonE :: PName -> Name -> NamingEnv
singletonE = singletonNS NSValue

-- | Singleton type renaming environment.
singletonT :: PName -> Name -> NamingEnv
singletonT = singletonNS NSType




instance Semigroup NamingEnv where
  NamingEnv l <> NamingEnv r =
      NamingEnv (Map.unionWith (Map.unionWith merge) l r)

instance Monoid NamingEnv where
  mempty = NamingEnv Map.empty
  {-# INLINE mempty #-}


-- | Merge two name maps, collapsing cases where the entries are the same, and
-- producing conflicts otherwise.
merge :: [Name] -> [Name] -> [Name]
merge xs ys | xs == ys  = xs
            | otherwise = nub (xs ++ ys)

-- | Generate a mapping from 'PrimIdent' to 'Name' for a
-- given naming environment.
toPrimMap :: NamingEnv -> PrimMap
toPrimMap env =
  PrimMap
    { primDecls = fromNS NSValue
    , primTypes = fromNS NSType
    }
  where
  fromNS ns = Map.fromList
                [ entry x | xs <- Map.elems (namespaceMap ns env), x <- xs ]

  entry n = case asPrim n of
              Just p  -> (p,n)
              Nothing -> panic "toPrimMap" [ "Not a declared name?"
                                           , show n
                                           ]


-- | Generate a display format based on a naming environment.
toNameDisp :: NamingEnv -> NameDisp
toNameDisp env = NameDisp display
  where
  display mn ident = Map.lookup (mn,ident) names

  -- XXX: Thid does not account for namespaces, so names can step on each other.
  -- only format declared names, as parameters don't need any special
  -- formatting.
  names = Map.fromList
            [ ((mn, nameIdent x), qn)
              | ns            <- [ NSValue, NSType, NSModule ]
              , (pn,xs)       <- Map.toList (namespaceMap ns env)
              , x             <- xs
              , Declared mn _ <- [nameInfo x]
              , let qn = case getModName pn of
                          Just q  -> Qualified q
                          Nothing -> UnQualified
            ]


-- | Produce sets of visible names for types and declarations.
--
-- NOTE: if entries in the NamingEnv would have produced a name clash,
-- they will be omitted from the resulting sets.
visibleNames :: NamingEnv -> Map Namespace (Set Name)
visibleNames (NamingEnv env) = Set.fromList . mapMaybe check . Map.elems <$> env
  where
  check names =
    case names of
      [name] -> Just name
      _      -> Nothing

-- | Qualify all symbols in a 'NamingEnv' with the given prefix.
qualify :: ModName -> NamingEnv -> NamingEnv
qualify pfx (NamingEnv env) = NamingEnv (Map.mapKeys toQual <$> env)
  where
  -- XXX we don't currently qualify fresh names
  toQual (Qual _ n)  = Qual pfx n
  toQual (UnQual n)  = Qual pfx n
  toQual n@NewName{} = n

filterNames :: (PName -> Bool) -> NamingEnv -> NamingEnv
filterNames p (NamingEnv env) = NamingEnv (Map.filterWithKey check <$> env)
  where check n _ = p n


-- | Like mappend, but when merging, prefer values on the lhs.
shadowing :: NamingEnv -> NamingEnv -> NamingEnv
shadowing (NamingEnv l) (NamingEnv r) = NamingEnv (Map.unionWith Map.union l r)

travNamingEnv :: Applicative f => (Name -> f Name) -> NamingEnv -> f NamingEnv
travNamingEnv f (NamingEnv mp) =
  NamingEnv <$> traverse (traverse (traverse f)) mp


data InModule a = InModule !ModName a
                  deriving (Functor,Traversable,Foldable,Show)


newTop :: FreshM m => ModName -> PName -> Maybe Fixity -> Range -> m Name
newTop ns thing fx rng = liftSupply (mkDeclared ns src (getIdent thing) fx rng)
  where src = if isGeneratedName thing then SystemName else UserName

newLocal :: FreshM m => PName -> Range -> m Name
newLocal thing rng = liftSupply (mkParameter (getIdent thing) rng)

newtype BuildNamingEnv = BuildNamingEnv { runBuild :: SupplyT Id NamingEnv }

buildNamingEnv :: BuildNamingEnv -> Supply -> (NamingEnv,Supply)
buildNamingEnv b supply = runId (runSupplyT supply (runBuild b))

-- | Generate a 'NamingEnv' using an explicit supply.
namingEnv' :: BindsNames a => a -> Supply -> (NamingEnv,Supply)
namingEnv' = buildNamingEnv . namingEnv



instance Semigroup BuildNamingEnv where
  BuildNamingEnv a <> BuildNamingEnv b = BuildNamingEnv $
    do x <- a
       y <- b
       return (mappend x y)

instance Monoid BuildNamingEnv where
  mempty = BuildNamingEnv (pure mempty)

  mappend = (<>)

  mconcat bs = BuildNamingEnv $
    do ns <- sequence (map runBuild bs)
       return (mconcat ns)

-- | Things that define exported names.
class BindsNames a where
  namingEnv :: a -> BuildNamingEnv

instance BindsNames NamingEnv where
  namingEnv env = BuildNamingEnv (return env)
  {-# INLINE namingEnv #-}

instance BindsNames a => BindsNames (Maybe a) where
  namingEnv = foldMap namingEnv
  {-# INLINE namingEnv #-}

instance BindsNames a => BindsNames [a] where
  namingEnv = foldMap namingEnv
  {-# INLINE namingEnv #-}

-- | Generate a type renaming environment from the parameters that are bound by
-- this schema.
instance BindsNames (Schema PName) where
  namingEnv (Forall ps _ _ _) = foldMap namingEnv ps
  {-# INLINE namingEnv #-}


-- | Interpret an import in the context of an interface, to produce a name
-- environment for the renamer, and a 'NameDisp' for pretty-printing.
interpImport :: Import     {- ^ The import declarations -} ->
                IfaceDecls {- ^ Declarations of imported module -} ->
                NamingEnv
interpImport imp publicDecls = qualified
  where

  -- optionally qualify names based on the import
  qualified | Just pfx <- iAs imp = qualify pfx restricted
            | otherwise           =             restricted

  -- restrict or hide imported symbols
  restricted
    | Just (Hiding ns) <- iSpec imp =
       filterNames (\qn -> not (getIdent qn `elem` ns)) public

    | Just (Only ns) <- iSpec imp =
       filterNames (\qn -> getIdent qn `elem` ns) public

    | otherwise = public

  -- generate the initial environment from the public interface, where no names
  -- are qualified
  public = unqualifiedEnv publicDecls


-- | Generate a naming environment from a declaration interface, where none of
-- the names are qualified.
unqualifiedEnv :: IfaceDecls -> NamingEnv
unqualifiedEnv IfaceDecls { .. } =
  mconcat [ exprs, tySyns, ntTypes, absTys, ntExprs ]
  where
  toPName n = mkUnqual (nameIdent n)

  exprs   = mconcat [ singletonE (toPName n) n | n <- Map.keys ifDecls ]
  tySyns  = mconcat [ singletonT (toPName n) n | n <- Map.keys ifTySyns ]
  ntTypes = mconcat [ singletonT (toPName n) n | n <- Map.keys ifNewtypes ]
  absTys  = mconcat [ singletonT (toPName n) n | n <- Map.keys ifAbstractTypes ]
  ntExprs = mconcat [ singletonE (toPName n) n | n <- Map.keys ifNewtypes ]


-- | Compute an unqualified naming environment, containing the various module
-- parameters.
modParamsNamingEnv :: IfaceParams -> NamingEnv
modParamsNamingEnv IfaceParams { .. } =
  NamingEnv $ Map.fromList
    [ (NSValue, Map.fromList $ map fromFu $ Map.keys ifParamFuns)
    , (NSType,  Map.fromList $ map fromTy $ Map.elems ifParamTypes)
    ]
  where
  toPName n = mkUnqual (nameIdent n)

  fromTy tp = let nm = T.mtpName tp
              in (toPName nm, [nm])

  fromFu f  = (toPName f, [f])



data ImportIface = ImportIface Import Iface

-- | Produce a naming environment from an interface file, that contains a
-- mapping only from unqualified names to qualified ones.
instance BindsNames ImportIface where
  namingEnv (ImportIface imp Iface { .. }) = BuildNamingEnv $
    return (interpImport imp ifPublic)
  {-# INLINE namingEnv #-}

-- | Introduce the name
instance BindsNames (InModule (Bind PName)) where
  namingEnv (InModule ns b) = BuildNamingEnv $
    do let Located { .. } = bName b
       n <- newTop ns thing (bFixity b) srcRange

       return (singletonE thing n)

-- | Generate the naming environment for a type parameter.
instance BindsNames (TParam PName) where
  namingEnv TParam { .. } = BuildNamingEnv $
    do let range = fromMaybe emptyRange tpRange
       n <- newLocal tpName range
       return (singletonT tpName n)

-- | The naming environment for a single module.  This is the mapping from
-- unqualified names to fully qualified names with uniques.
instance BindsNames (Module PName) where
  namingEnv Module { .. } = foldMap (namingEnv . InModule ns) mDecls
    where
    ns = thing mName

instance BindsNames (InModule (TopDecl PName)) where
  namingEnv (InModule ns td) =
    case td of
      Decl d           -> namingEnv (InModule ns (tlValue d))
      DPrimType d      -> namingEnv (InModule ns (tlValue d))
      TDNewtype d      -> namingEnv (InModule ns (tlValue d))
      DParameterType d -> namingEnv (InModule ns d)
      DParameterConstraint {} -> mempty
      DParameterFun  d -> namingEnv (InModule ns d)
      Include _   -> mempty

instance BindsNames (InModule (PrimType PName)) where
  namingEnv (InModule ns PrimType { .. }) =
    BuildNamingEnv $
      do let Located { .. } = primTName
         nm <- newTop ns thing primTFixity srcRange
         pure (singletonT thing nm)

instance BindsNames (InModule (ParameterFun PName)) where
  namingEnv (InModule ns ParameterFun { .. }) = BuildNamingEnv $
    do let Located { .. } = pfName
       ntName <- newTop ns thing pfFixity srcRange
       return (singletonE thing ntName)

instance BindsNames (InModule (ParameterType PName)) where
  namingEnv (InModule ns ParameterType { .. }) = BuildNamingEnv $
    -- XXX: we don't seem to have a fixity environment at the type level
    do let Located { .. } = ptName
       ntName <- newTop ns thing Nothing srcRange
       return (singletonT thing ntName)

-- NOTE: we use the same name at the type and expression level, as there's only
-- ever one name introduced in the declaration. The names are only ever used in
-- different namespaces, so there's no ambiguity.
instance BindsNames (InModule (Newtype PName)) where
  namingEnv (InModule ns Newtype { .. }) = BuildNamingEnv $
    do let Located { .. } = nName
       ntName <- newTop ns thing Nothing srcRange
       return (singletonT thing ntName `mappend` singletonE thing ntName)

-- | The naming environment for a single declaration.
instance BindsNames (InModule (Decl PName)) where
  namingEnv (InModule pfx d) = case d of
    DBind b -> BuildNamingEnv $
      do n <- mkName (bName b) (bFixity b)
         return (singletonE (thing (bName b)) n)

    DSignature ns _sig      -> foldMap qualBind ns
    DPragma ns _p           -> foldMap qualBind ns
    DType syn               -> qualType (tsName syn) (tsFixity syn)
    DProp syn               -> qualType (psName syn) (psFixity syn)
    DLocated d' _           -> namingEnv (InModule pfx d')
    DPatBind _pat _e        -> panic "ModuleSystem" ["Unexpected pattern binding"]
    DFixity{}               -> panic "ModuleSystem" ["Unexpected fixity declaration"]

    where

    mkName ln fx = newTop pfx (thing ln) fx (srcRange ln)

    qualBind ln = BuildNamingEnv $
      do n <- mkName ln Nothing
         return (singletonE (thing ln) n)

    qualType ln f = BuildNamingEnv $
      do n <- mkName ln f
         return (singletonT (thing ln) n)

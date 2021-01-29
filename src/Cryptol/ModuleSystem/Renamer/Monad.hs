-- |
-- Module      :  Cryptol.ModuleSystem.Renamer
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# Language RecordWildCards #-}
{-# Language FlexibleContexts #-}
module Cryptol.ModuleSystem.Renamer.Monad where

import Data.List(sort)
import qualified Data.Foldable as F
import           Data.Map.Strict ( Map )
import qualified Data.Map.Strict as Map
import qualified Data.Sequence as Seq
import qualified Data.Semigroup as S
import qualified Data.Set as Set
import           MonadLib hiding (mapM, mapM_)

import Prelude ()
import Prelude.Compat

import Cryptol.ModuleSystem.Name
import Cryptol.ModuleSystem.NamingEnv
import Cryptol.ModuleSystem.Interface
import Cryptol.Parser.AST
import Cryptol.Parser.Position
import Cryptol.Utils.Panic (panic)

import Cryptol.ModuleSystem.Renamer.Error

-- | Information needed to do some renaming.
data RenamerInfo = RenamerInfo
  { renSupply   :: Supply     -- ^ Use to make new names
  , renContext  :: ModPath    -- ^ We are renaming things in here
  , renEnv      :: NamingEnv  -- ^ This is what's in scope
  , renIfaces   :: ModName -> Iface
  }

newtype RenameM a = RenameM { unRenameM :: ReaderT RO (StateT RW Lift) a }

data RO = RO
  { roLoc    :: Range
  , roMod    :: !ModPath
  , roNames  :: NamingEnv
  , roIfaces :: ModName -> Iface
  }

data RW = RW
  { rwWarnings      :: ![RenamerWarning]
  , rwErrors        :: !(Seq.Seq RenamerError)
  , rwSupply        :: !Supply
  , rwNameUseCount  :: !(Map Name Int)
    -- ^ How many times did we refer to each name.
    -- Used to generate warnings for unused definitions.
  }




instance S.Semigroup a => S.Semigroup (RenameM a) where
  {-# INLINE (<>) #-}
  a <> b =
    do x <- a
       y <- b
       return (x S.<> y)

instance (S.Semigroup a, Monoid a) => Monoid (RenameM a) where
  {-# INLINE mempty #-}
  mempty = return mempty

  {-# INLINE mappend #-}
  mappend = (S.<>)

instance Functor RenameM where
  {-# INLINE fmap #-}
  fmap f m      = RenameM (fmap f (unRenameM m))

instance Applicative RenameM where
  {-# INLINE pure #-}
  pure x        = RenameM (pure x)

  {-# INLINE (<*>) #-}
  l <*> r       = RenameM (unRenameM l <*> unRenameM r)

instance Monad RenameM where
  {-# INLINE return #-}
  return x      = RenameM (return x)

  {-# INLINE (>>=) #-}
  m >>= k       = RenameM (unRenameM m >>= unRenameM . k)

instance FreshM RenameM where
  liftSupply f = RenameM $ sets $ \ RW { .. } ->
    let (a,s') = f rwSupply
        rw'    = RW { rwSupply = s', .. }
     in a `seq` rw' `seq` (a, rw')


runRenamer :: RenamerInfo -> RenameM a
           -> (Either [RenamerError] (a,Supply),[RenamerWarning])
runRenamer info m = (res, warns)
  where
  warns = sort (rwWarnings rw ++ warnUnused (renContext info) (renEnv info) rw)

  (a,rw) = runM (unRenameM m) ro
                              RW { rwErrors   = Seq.empty
                                 , rwWarnings = []
                                 , rwSupply   = renSupply info
                                 , rwNameUseCount = Map.empty
                                 }

  ro = RO { roLoc   = emptyRange
          , roNames = renEnv info
          , roMod   = renContext info
          , roIfaces = renIfaces info
          }

  res | Seq.null (rwErrors rw) = Right (a,rwSupply rw)
      | otherwise              = Left (F.toList (rwErrors rw))

-- | Record an error.  XXX: use a better name
record :: RenamerError -> RenameM ()
record f = RenameM $
  do RW { .. } <- get
     set RW { rwErrors = rwErrors Seq.|> f, .. }



-- | Get the source range for wahtever we are currently renaming.
curLoc :: RenameM Range
curLoc  = RenameM (roLoc `fmap` ask)

-- | Annotate something with the current range.
located :: a -> RenameM (Located a)
located thing =
  do srcRange <- curLoc
     return Located { .. }

-- | Do the given computation using the source code range from `loc` if any.
withLoc :: HasLoc loc => loc -> RenameM a -> RenameM a
withLoc loc m = RenameM $ case getLoc loc of

  Just range -> do
    ro <- ask
    local ro { roLoc = range } (unRenameM m)

  Nothing -> unRenameM m

-- | Retrieve the name of the current module.
getNS :: RenameM ModPath
getNS  = RenameM (roMod `fmap` ask)

-- | Shadow the current naming environment with some more names.
shadowNames :: BindsNames env => env -> RenameM a -> RenameM a
shadowNames  = shadowNames' CheckAll

data EnvCheck = CheckAll     -- ^ Check for overlap and shadowing
              | CheckOverlap -- ^ Only check for overlap
              | CheckNone    -- ^ Don't check the environment
                deriving (Eq,Show)

-- | Shadow the current naming environment with some more names.
shadowNames' :: BindsNames env => EnvCheck -> env -> RenameM a -> RenameM a
shadowNames' check names m = do
  do env <- liftSupply (namingEnv' names)
     RenameM $
       do ro  <- ask
          env' <- sets (checkEnv check env (roNames ro))
          let ro' = ro { roNames = env' `shadowing` roNames ro }
          local ro' (unRenameM m)

shadowNamesNS :: BindsNames (InModule env) => env -> RenameM a -> RenameM a
shadowNamesNS names m =
  do ns <- getNS
     shadowNames (InModule ns names) m


-- | Generate warnings when the left environment shadows things defined in
-- the right.  Additionally, generate errors when two names overlap in the
-- left environment.
checkEnv :: EnvCheck -> NamingEnv -> NamingEnv -> RW -> (NamingEnv,RW)
checkEnv check (NamingEnv lenv) r rw0
  | check == CheckNone = (newEnv,rw0)
  | otherwise          = (newEnv,rwFin)

  where
  newEnv         = NamingEnv newMap
  (rwFin,newMap) = Map.mapAccumWithKey doNS rw0 lenv
  doNS rw ns     = Map.mapAccumWithKey (step ns) rw

  step ns acc k xs = (acc', [head xs])
    where
    acc' = acc
      { rwWarnings =
          if check == CheckAll
             then case Map.lookup k (namespaceMap ns r) of
                    Just os | [x] <- xs ->
                                        SymbolShadowed k x os : rwWarnings acc
                    _ -> rwWarnings acc

             else rwWarnings acc
      , rwErrors   = rwErrors acc Seq.>< containsOverlap xs
      }

-- | Check the RHS of a single name rewrite for conflicting sources.
containsOverlap :: [Name] -> Seq.Seq RenamerError
containsOverlap [_] = Seq.empty
containsOverlap []  = panic "Renamer" ["Invalid naming environment"]
containsOverlap ns  = Seq.singleton (OverlappingSyms ns)


recordUse :: Name -> RenameM ()
recordUse x = RenameM $ sets_ $ \rw ->
  rw { rwNameUseCount = Map.insertWith (+) x 1 (rwNameUseCount rw) }


warnUnused :: ModPath -> NamingEnv -> RW -> [RenamerWarning]
warnUnused m0 env rw =
  map warn
  $ Map.keys
  $ Map.filterWithKey keep
  $ rwNameUseCount rw
  where
  warn x   = UnusedName x
  keep k n = n == 1 && isLocal k
  oldNames = Map.findWithDefault Set.empty NSType (visibleNames env)
  isLocal nm = case nameInfo nm of
                 Declared m sys -> sys == UserName &&
                                   m == m0 && nm `Set.notMember` oldNames
                 Parameter  -> True

lookupImport :: Import -> RenameM (IfaceDecls, NamingEnv)
lookupImport imp = RenameM $
  do getIf <- roIfaces <$> ask
     let ds = ifPublic (getIf (iModule imp))
     pure (ds, interpImport imp ds)


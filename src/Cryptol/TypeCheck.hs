-- |
-- Module      :  Cryptol.TypeCheck
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable
{-# LANGUAGE PatternGuards, OverloadedStrings #-}

module Cryptol.TypeCheck
  ( tcModule
  , tcModuleInst
  , tcExpr
  , tcDecls
  , InferInput(..)
  , InferOutput(..)
  , SolverConfig(..)
  , NameSeeds
  , nameSeeds
  , Error(..)
  , Warning(..)
  , ppWarning
  , ppError
  , WithNames(..)
  , NameMap
  , ppNamedWarning
  , ppNamedError
  ) where

import           Cryptol.ModuleSystem.Name
                    (liftSupply,mkDeclared,NameSource(..),ModPath(..))
import qualified Cryptol.Parser.AST as P
import           Cryptol.Parser.Position(Range,emptyRange)
import           Cryptol.TypeCheck.AST
import           Cryptol.TypeCheck.Depends (FromDecl)
import           Cryptol.TypeCheck.Error
import           Cryptol.TypeCheck.Monad
                   ( runInferM
                   , InferInput(..)
                   , InferOutput(..)
                   , NameSeeds
                   , nameSeeds
                   , lookupVar
                   )
import           Cryptol.TypeCheck.Infer (inferModule, inferBinds, inferDs)
import           Cryptol.TypeCheck.InferTypes(VarType(..), SolverConfig(..))
import           Cryptol.TypeCheck.Solve(proveModuleTopLevel)
import           Cryptol.TypeCheck.CheckModuleInstance(checkModuleInstance)
import           Cryptol.TypeCheck.Monad(withParamType,withParameterConstraints)
import           Cryptol.TypeCheck.PP(WithNames(..),NameMap)
import           Cryptol.Utils.Ident (exprModName,packIdent,Namespace(..))
import           Cryptol.Utils.PP
import           Cryptol.Utils.Panic(panic)

tcModule :: P.Module Name -> InferInput -> IO (InferOutput Module)
tcModule m inp = runInferM inp (inferModule m)

-- | Check a module instantiation, assuming that the functor has already
-- been checked.
tcModuleInst :: Module                  {- ^ functor -} ->
                P.Module Name           {- params -} ->
                InferInput              {- ^ TC settings -} ->
                IO (InferOutput Module) {- ^ new version of instance -}
tcModuleInst func m inp = runInferM inp
                        $ do x <- inferModule m
                             flip (foldr withParamType) (mParamTypes x) $
                               withParameterConstraints (mParamConstraints x) $
                               do y <- checkModuleInstance func x
                                  proveModuleTopLevel
                                  pure y

tcExpr :: P.Expr Name -> InferInput -> IO (InferOutput (Expr,Schema))
tcExpr e0 inp = runInferM inp
                $ do x <- go emptyRange e0
                     proveModuleTopLevel
                     return x

  where
  go loc expr =
    case expr of
      P.ELocated e loc' ->
        do (te, sch) <- go loc' e
           pure $! if inpCallStacks inp then (ELocated loc' te, sch) else (te,sch)
      P.EVar x  ->
        do res <- lookupVar x
           case res of
             ExtVar s    -> return (EVar x, s)
             CurSCC e' t -> panic "Cryptol.TypeCheck.tcExpr"
                             [ "CurSCC outside binder checking:"
                             , show e'
                             , show t
                             ]
      _ -> do fresh <- liftSupply $
                        mkDeclared NSValue (TopModule exprModName) SystemName
                                      (packIdent "(expression)") Nothing loc
              res   <- inferBinds True False
                [ P.Bind
                    { P.bName      = P.Located { P.srcRange = loc, P.thing = fresh }
                    , P.bParams    = []
                    , P.bDef       = P.Located (inpRange inp) (P.DExpr expr)
                    , P.bPragmas   = []
                    , P.bSignature = Nothing
                    , P.bMono      = False
                    , P.bInfix     = False
                    , P.bFixity    = Nothing
                    , P.bDoc       = Nothing
                    } ]

              case res of
                [d] | DExpr e <- dDefinition d -> return (e, dSignature d)
                    | otherwise                ->
                       panic "Cryptol.TypeCheck.tcExpr"
                          [ "Expected an expression in definition"
                          , show d ]

                _   -> panic "Cryptol.TypeCheck.tcExpr"
                          ( "Multiple declarations when check expression:"
                          : map show res
                          )

tcDecls :: FromDecl d => [d] -> InferInput -> IO (InferOutput [DeclGroup])
tcDecls ds inp = runInferM inp $ inferDs ds $ \dgs -> do
                   proveModuleTopLevel
                   return dgs

ppWarning :: (Range,Warning) -> Doc
ppWarning (r,w) = text "[warning] at" <+> pp r <.> colon $$ nest 2 (pp w)

ppError :: (Range,Error) -> Doc
ppError (r,w) = text "[error] at" <+> pp r <.> colon $$ nest 2 (pp w)


ppNamedWarning :: NameMap -> (Range,Warning) -> Doc
ppNamedWarning nm (r,w) =
  text "[warning] at" <+> pp r <.> colon $$ nest 2 (pp (WithNames w nm))

ppNamedError :: NameMap -> (Range,Error) -> Doc
ppNamedError nm (r,e) =
  text "[error] at" <+> pp r <.> colon $$ nest 2 (pp (WithNames e nm))



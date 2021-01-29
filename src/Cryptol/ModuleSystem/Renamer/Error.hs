-- |
-- Module      :  Cryptol.ModuleSystem.Renamer
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# Language DeriveGeneric, DeriveAnyClass #-}
{-# Language OverloadedStrings #-}
module Cryptol.ModuleSystem.Renamer.Error where

import Cryptol.ModuleSystem.Name
import Cryptol.Parser.AST
import Cryptol.Parser.Position
import Cryptol.Parser.Selector(ppNestedSels)
import Cryptol.Utils.PP

import GHC.Generics (Generic)
import Control.DeepSeq

import Prelude ()
import Prelude.Compat

-- Errors ----------------------------------------------------------------------

data RenamerError
  = MultipleSyms (Located PName) [Name]
    -- ^ Multiple imported symbols contain this name

  | UnboundExpr (Located PName)
    -- ^ Expression name is not bound to any definition

  | UnboundType (Located PName)
    -- ^ Type name is not bound to any definition

  | OverlappingSyms [Name]
    -- ^ An environment has produced multiple overlapping symbols

  | ExpectedValue (Located PName)
    -- ^ When a value is expected from the naming environment, but one or more
    -- types exist instead.

  | ExpectedType (Located PName)
    -- ^ When a type is missing from the naming environment, but one or more
    -- values exist with the same name.

  | FixityError (Located Name) Fixity (Located Name) Fixity
    -- ^ When the fixity of two operators conflict

  | InvalidConstraint (Type PName)
    -- ^ When it's not possible to produce a Prop from a Type.

  | MalformedBuiltin (Type PName) PName
    -- ^ When a builtin type/type-function is used incorrectly.

  | BoundReservedType PName (Maybe Range) Doc
    -- ^ When a builtin type is named in a binder.

  | OverlappingRecordUpdate (Located [Selector]) (Located [Selector])
    -- ^ When record updates overlap (e.g., @{ r | x = e1, x.y = e2 }@)
    deriving (Show, Generic, NFData)

instance PP RenamerError where
  ppPrec _ e = case e of

    MultipleSyms lqn qns ->
      hang (text "[error] at" <+> pp (srcRange lqn))
         4 $ (text "Multiple definitions for symbol:" <+> pp (thing lqn))
          $$ vcat (map ppLocName qns)

    UnboundExpr lqn ->
      hang (text "[error] at" <+> pp (srcRange lqn))
         4 (text "Value not in scope:" <+> pp (thing lqn))

    UnboundType lqn ->
      hang (text "[error] at" <+> pp (srcRange lqn))
         4 (text "Type not in scope:" <+> pp (thing lqn))

    OverlappingSyms qns ->
      hang (text "[error]")
         4 $ text "Overlapping symbols defined:"
          $$ vcat (map ppLocName qns)

    ExpectedValue lqn ->
      hang (text "[error] at" <+> pp (srcRange lqn))
         4 (fsep [ text "Expected a value named", quotes (pp (thing lqn))
                 , text "but found a type instead"
                 , text "Did you mean `(" <.> pp (thing lqn) <.> text")?" ])

    ExpectedType lqn ->
      hang (text "[error] at" <+> pp (srcRange lqn))
         4 (fsep [ text "Expected a type named", quotes (pp (thing lqn))
                 , text "but found a value instead" ])

    FixityError o1 f1 o2 f2 ->
      hang (text "[error] at" <+> pp (srcRange o1) <+> text "and" <+> pp (srcRange o2))
         4 (fsep [ text "The fixities of"
                 , nest 2 $ vcat
                   [ "•" <+> pp (thing o1) <+> parens (pp f1)
                   , "•" <+> pp (thing o2) <+> parens (pp f2) ]
                 , text "are not compatible."
                 , text "You may use explicit parentheses to disambiguate." ])

    InvalidConstraint ty ->
      hang (text "[error]" <+> maybe empty (\r -> text "at" <+> pp r) (getLoc ty))
         4 (fsep [ pp ty, text "is not a valid constraint" ])

    MalformedBuiltin ty pn ->
      hang (text "[error]" <+> maybe empty (\r -> text "at" <+> pp r) (getLoc ty))
         4 (fsep [ text "invalid use of built-in type", pp pn
                 , text "in type", pp ty ])

    BoundReservedType n loc src ->
      hang (text "[error]" <+> maybe empty (\r -> text "at" <+> pp r) loc)
         4 (fsep [ text "built-in type", quotes (pp n), text "shadowed in", src ])

    OverlappingRecordUpdate xs ys ->
      hang "[error] Overlapping record updates:"
         4 (vcat [ ppLab xs, ppLab ys ])
      where
      ppLab as = ppNestedSels (thing as) <+> "at" <+> pp (srcRange as)

-- Warnings --------------------------------------------------------------------

data RenamerWarning
  = SymbolShadowed PName Name [Name]
  | UnusedName Name
    deriving (Show, Generic, NFData)

instance Eq RenamerWarning where
  x == y = compare x y == EQ

-- used to determine in what order ot show things
instance Ord RenamerWarning where
  compare w1 w2 =
    case w1 of
      SymbolShadowed x y _ ->
        case w2 of
          SymbolShadowed x' y' _ -> compare (byStart y,x) (byStart y',x')
          _                      -> LT
      UnusedName x ->
        case w2 of
          UnusedName y -> compare (byStart x) (byStart y)
          _            -> GT

      where
      byStart = from . nameLoc


instance PP RenamerWarning where
  ppPrec _ (SymbolShadowed k x os) =
    hang (text "[warning] at" <+> loc)
       4 $ fsep [ "This binding for" <+> backticks (pp k)
                , "shadows the existing binding" <.> plural
                , text "at" ]
        $$ vcat (map (pp . nameLoc) os)

    where
    plural | length os > 1 = char 's'
           | otherwise     = empty

    loc = pp (nameLoc x)

  ppPrec _ (UnusedName x) =
    hang (text "[warning] at" <+> pp (nameLoc x))
       4 (text "Unused name:" <+> pp x)




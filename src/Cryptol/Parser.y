{
-- |
-- Module      :  Cryptol.Parser
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Trustworthy #-}
module Cryptol.Parser
  ( parseModule
  , parseProgram, parseProgramWith
  , parseExpr, parseExprWith
  , parseDecl, parseDeclWith
  , parseDecls, parseDeclsWith
  , parseLetDecl, parseLetDeclWith
  , parseRepl, parseReplWith
  , parseSchema, parseSchemaWith
  , parseModName, parseHelpName
  , ParseError(..), ppError
  , Layout(..)
  , Config(..), defaultConfig
  , guessPreProc, PreProc(..)
  ) where

import           Control.Applicative as A
import           Data.Maybe(fromMaybe)
import           Data.Text(Text)
import qualified Data.Text as T
import           Control.Monad(liftM2,msum)

import Cryptol.Prims.Syntax(TFun(..))
import Cryptol.Parser.AST
import Cryptol.Parser.Position
import Cryptol.Parser.LexerUtils hiding (mkIdent)
import Cryptol.Parser.ParserUtils
import Cryptol.Parser.Unlit(PreProc(..), guessPreProc)
import Cryptol.Utils.Ident(paramInstModName)

import Paths_cryptol
}


%token
  NUM         { $$@(Located _ (Token (Num   {}) _))}
  STRLIT      { $$@(Located _ (Token (StrLit {}) _))}
  CHARLIT     { $$@(Located _ (Token (ChrLit {}) _))}

  IDENT       { $$@(Located _ (Token (Ident [] _) _))}
  QIDENT      { $$@(Located _ (Token  Ident{}     _))}

  'include'   { Located $$ (Token (KW KW_include)   _)}
  'import'    { Located $$ (Token (KW KW_import)    _)}
  'as'        { Located $$ (Token (KW KW_as)        _)}
  'hiding'    { Located $$ (Token (KW KW_hiding)    _)}
  'private'   { Located $$ (Token (KW KW_private)   _)}
  'parameter' { Located $$ (Token (KW KW_parameter) _)}
  'property'  { Located $$ (Token (KW KW_property)  _)}
  'infix'     { Located $$ (Token (KW KW_infix)     _)}
  'infixl'    { Located $$ (Token (KW KW_infixl)    _)}
  'infixr'    { Located $$ (Token (KW KW_infixr)    _)}

  'type'      { Located $$ (Token (KW KW_type   ) _)}
  'newtype'   { Located $$ (Token (KW KW_newtype) _)}
  'module'    { Located $$ (Token (KW KW_module ) _)}
  'where'     { Located $$ (Token (KW KW_where  ) _)}
  'let'       { Located $$ (Token (KW KW_let    ) _)}
  'if'        { Located $$ (Token (KW KW_if     ) _)}
  'then'      { Located $$ (Token (KW KW_then   ) _)}
  'else'      { Located $$ (Token (KW KW_else   ) _)}
  'x'         { Located $$ (Token (KW KW_x)       _)}

  'primitive' { Located $$ (Token (KW KW_primitive) _)}
  'constraint'{ Located $$ (Token (KW KW_constraint) _)}

  '['         { Located $$ (Token (Sym BracketL) _)}
  ']'         { Located $$ (Token (Sym BracketR) _)}
  '<-'        { Located $$ (Token (Sym ArrL    ) _)}
  '..'        { Located $$ (Token (Sym DotDot  ) _)}
  '...'       { Located $$ (Token (Sym DotDotDot) _)}
  '|'         { Located $$ (Token (Sym Bar     ) _)}

  '('         { Located $$ (Token (Sym ParenL  ) _)}
  ')'         { Located $$ (Token (Sym ParenR  ) _)}
  ','         { Located $$ (Token (Sym Comma   ) _)}
  ';'         { Located $$ (Token (Sym Semi    ) _)}
  '.'         { Located $$ (Token (Sym Dot     ) _)}
  '{'         { Located $$ (Token (Sym CurlyL  ) _)}
  '}'         { Located $$ (Token (Sym CurlyR  ) _)}
  '<|'        { Located $$ (Token (Sym TriL    ) _)}
  '|>'        { Located $$ (Token (Sym TriR    ) _)}
  '='         { Located $$ (Token (Sym EqDef   ) _)}
  '`'         { Located $$ (Token (Sym BackTick) _)}
  ':'         { Located $$ (Token (Sym Colon   ) _)}
  '->'        { Located $$ (Token (Sym ArrR    ) _)}
  '=>'        { Located $$ (Token (Sym FatArrR ) _)}
  '\\'        { Located $$ (Token (Sym Lambda  ) _)}
  '_'         { Located $$ (Token (Sym Underscore ) _)}


  'v{'        { Located $$ (Token (Virt VCurlyL)  _)}
  'v}'        { Located $$ (Token (Virt VCurlyR)  _)}
  'v;'        { Located $$ (Token (Virt VSemi)    _)}

  '+'         { Located $$ (Token (Op Plus)  _)}
  '*'         { Located $$ (Token (Op Mul)   _)}
  '^^'        { Located $$ (Token (Op Exp)   _)}

  '-'         { Located $$ (Token (Op Minus) _)}
  '~'         { Located $$ (Token (Op Complement) _)}

  '#'         { Located $$ (Token (Op Hash) _)}

  OP          { $$@(Located _ (Token (Op (Other [] _)) _))}
  QOP         { $$@(Located _ (Token (Op  Other{}   )  _))}

  DOC         { $$@(Located _ (Token (White DocStr) _)) }

%name vmodule vmodule
%name program program
%name programLayout program_layout
%name expr    expr
%name decl    decl
%name decls   decls
%name declsLayout decls_layout
%name letDecl let_decl
%name repl    repl
%name schema  schema
%name modName modName
%name helpName help_name
%tokentype { Located Token }
%monad { ParseM }
%lexer { lexerP } { Located _ (Token EOF _) }

{- If you add additional operators, please update the corresponding
   tables in the pretty printer. -}

%nonassoc '=>'
%right '->'
%left     'where'
%nonassoc 'then' 'else'
%nonassoc ':'
%nonassoc '=='
%nonassoc '<=' '>='
%right '#'
%left  '+' '-'
%left  '*' '/' '%'
%right '^^'
%right NEG '~'
%left OP QOP
%%


vmodule                    :: { Module PName }
  : 'module' modName 'where' 'v{' vmod_body 'v}' { mkModule $2 $5 }
  | 'module' modName '=' modName 'where' 'v{' vmod_body 'v}'
                                                 { mkModuleInstance $2 $4 $7 }
  | 'v{' vmod_body 'v}'                          { mkAnonymousModule $2 }

vmod_body                  :: { ([Located Import], [TopDecl PName]) }
  : vimports 'v;' vtop_decls  { (reverse $1, reverse $3) }
  | vimports ';'  vtop_decls  { (reverse $1, reverse $3) }
  | vimports                  { (reverse $1, [])         }
  | vtop_decls                { ([], reverse $1)         }
  | {- empty -}               { ([], [])                 }

vimports                   :: { [Located Import] }
  : vimports 'v;' import      { $3 : $1 }
  | vimports ';'  import      { $3 : $1 }
  | import                    { [$1]    }

-- XXX replace rComb with uses of at
import                     :: { Located Import }
  : 'import' modName mbAs mbImportSpec optWhere
                              { Located { srcRange = rComb $1
                                                   $ fromMaybe (srcRange $2)
                                                   $ msum [ fmap srcRange $4
                                                          , fmap srcRange $3
                                                          ]
                                        , thing    = Import
                                          { iModule    = thing $2
                                          , iAs        = fmap thing $3
                                          , iSpec      = fmap thing $4
                                          , iWhere     = $5
                                          }
                                        } }

optWhere ::  { [Decl PName] }
  : 'where' '{' '}'            { [] }
  | 'where' '{' decls '}'      { [] }
  | 'where' 'v{' 'v}'          { [] }
  | 'where' 'v{' vdecls 'v}'   { $3 }
  | {- empty -}                { [] }

mbAs                       :: { Maybe (Located ModName) }
  : 'as' modName              { Just $2 }
  | {- empty -}               { Nothing }

mbImportSpec               :: { Maybe (Located ImportSpec) }
  : mbHiding '(' name_list ')'{ Just Located
                                  { srcRange = case $3 of
                                      { [] -> emptyRange
                                      ; xs -> rCombs (map srcRange xs) }
                                  , thing    = $1 (reverse (map thing $3))
                                  } }
  | {- empty -}               { Nothing }

name_list                  :: { [LIdent] }
  : name_list ',' ident       { $3 : $1 }
  | ident                     { [$1]    }
  | {- empty -}               { []      }

mbHiding                   :: { [Ident] -> ImportSpec }
  : 'hiding'                  { Hiding }
  | {- empty -}               { Only   }

program                    :: { Program PName }
  : top_decls                 { Program (reverse $1) }
  | {- empty -}               { Program [] }

program_layout             :: { Program PName }
  : 'v{' vtop_decls 'v}'      { Program (reverse $2) }
  | 'v{''v}'                  { Program []           }

top_decls                  :: { [TopDecl PName]  }
  : top_decl ';'              { $1         }
  | top_decls top_decl ';'    { $2 ++ $1   }

vtop_decls                 :: { [TopDecl PName]  }
  : vtop_decl                 { $1       }
  | vtop_decls 'v;' vtop_decl { $3 ++ $1 }
  | vtop_decls ';'  vtop_decl { $3 ++ $1 }

vtop_decl               :: { [TopDecl PName] }
  : decl                   { [exportDecl Nothing   Public $1]                 }
  | doc decl               { [exportDecl (Just $1) Public $2]                 }
  | mbDoc 'include' STRLIT {% (return . Include) `fmap` fromStrLit $3         }
  | mbDoc 'property' name apats '=' expr
                           { [exportDecl $1 Public (mkProperty $3 $4 $6)]     }
  | mbDoc 'property' name       '=' expr
                           { [exportDecl $1 Public (mkProperty $3 [] $5)]     }
  | mbDoc newtype          { [exportNewtype Public $1 $2]                     }
  | prim_bind              { $1                                               }
  | private_decls          { $1                                               }
  | parameter_decls        { $1                                               }

top_decl                :: { [TopDecl PName] }
  : decl                   { [Decl (TopLevel {tlExport = Public, tlValue = $1 })] }
  | 'include' STRLIT       {% (return . Include) `fmap` fromStrLit $2             }
  | prim_bind              { $1                                                   }

private_decls           :: { [TopDecl PName] }
  : 'private' 'v{' vtop_decls 'v}'
                           { changeExport Private (reverse $3)                }
  | doc 'private' 'v{' vtop_decls 'v}'
                           { changeExport Private (reverse $4)                }

prim_bind               :: { [TopDecl PName] }
  : mbDoc 'primitive' name  ':' schema       { mkPrimDecl $1 $3 $5 }
  | mbDoc 'primitive' '(' op ')' ':' schema  { mkPrimDecl $1 $4 $7 }



parameter_decls                      :: { [TopDecl PName] }
  :     'parameter' 'v{' par_decls 'v}' { reverse $3 }
  | doc 'parameter' 'v{' par_decls 'v}' { reverse $4 }

-- Reversed
par_decls                            :: { [TopDecl PName] }
  : par_decl                            { [$1] }
  | par_decls ';'  par_decl             { $3 : $1 }
  | par_decls 'v;' par_decl             { $3 : $1 }

par_decl                         :: { TopDecl PName }
  : mbDoc        name ':' schema    { mkParFun $1 $2 $4 }
  | mbDoc 'type' name ':' kind      {% mkParType $1 $3 $5 }
  | mbDoc 'type' 'constraint' type  {% fmap (DParameterConstraint . distrLoc)
                                            (mkProp $4) }


doc                     :: { Located String }
  : DOC                    { mkDoc (fmap tokenText $1) }

mbDoc                   :: { Maybe (Located String) }
  : doc                    { Just $1 }
  | {- empty -}            { Nothing }


decl                    :: { Decl PName }
  : vars_comma ':' schema  { at (head $1,$3) $ DSignature (reverse $1) $3   }
  | ipat '=' expr          { at ($1,$3) $ DPatBind $1 $3                    }
  | '(' op ')' '=' expr    { at ($1,$5) $ DPatBind (PVar $2) $5             }
  | var apats '=' expr     { at ($1,$4) $
                             DBind $ Bind { bName      = $1
                                          , bParams    = reverse $2
                                          , bDef       = at $4 (Located emptyRange (DExpr $4))
                                          , bSignature = Nothing
                                          , bPragmas   = []
                                          , bMono      = False
                                          , bInfix     = False
                                          , bFixity    = Nothing
                                          , bDoc       = Nothing
                                          } }

  | apat pat_op apat '=' expr
                           { at ($1,$5) $
                             DBind $ Bind { bName      = $2
                                          , bParams    = [$1,$3]
                                          , bDef       = at $5 (Located emptyRange (DExpr $5))
                                          , bSignature = Nothing
                                          , bPragmas   = []
                                          , bMono      = False
                                          , bInfix     = True
                                          , bFixity    = Nothing
                                          , bDoc       = Nothing
                                          } }

  | 'type' name '=' type   {% at ($1,$4) `fmap` mkTySyn $2 [] $4 }
  | 'type' name tysyn_params '=' type
                           {% at ($1,$5) `fmap` mkTySyn $2 (reverse $3) $5  }

  | 'type' 'constraint' name '=' type
                           {% at ($2,$5) `fmap` mkPropSyn $3 [] $5 }
  | 'type' 'constraint' name tysyn_params '=' type
                           {% at ($2,$6) `fmap` mkPropSyn $3 (reverse $4) $6 }

  | 'infixl' NUM ops       {% mkFixity LeftAssoc  $2 (reverse $3) }
  | 'infixr' NUM ops       {% mkFixity RightAssoc $2 (reverse $3) }
  | 'infix'  NUM ops       {% mkFixity NonAssoc   $2 (reverse $3) }
  | error                  {% expected "a declaration" }

let_decl                :: { Decl PName }
  : 'let' ipat '=' expr          { at ($2,$4) $ DPatBind $2 $4                    }
  | 'let' name apats '=' expr    { at ($2,$5) $
                                   DBind $ Bind { bName      = $2
                                                , bParams    = reverse $3
                                                , bDef       = at $5 (Located emptyRange (DExpr $5))
                                                , bSignature = Nothing
                                                , bPragmas   = []
                                                , bMono      = False
                                                , bInfix     = False
                                                , bFixity    = Nothing
                                                , bDoc       = Nothing
                                                } }

newtype                 :: { Newtype PName }
  : 'newtype' qname '=' newtype_body
                           { Newtype { nName = $2, nParams = [], nBody = $4 } }
  | 'newtype' qname tysyn_params '=' newtype_body
                           { Newtype { nName = $2, nParams = $3, nBody = $5 } }

newtype_body            :: { [Named (Type PName)] }
  : '{' '}'                { [] }
  | '{' field_types '}'    { $2 }

vars_comma                 :: { [ LPName ]  }
  : var                       { [ $1]      }
  | vars_comma ',' var        { $3 : $1    }

var                        :: { LPName }
  : name                      { $1 }
  | '(' op ')'                { $2 }

apats                     :: { [Pattern PName] }
  : apat                   { [$1] }
  | apats1 apat            { $2 : $1 }

apats1                   :: { [Pattern PName]  }
  : apat                    { [$1]       }
  | apats1 apat             { $2 : $1    }

decls                   :: { [Decl PName] }
  : decl ';'               { [$1] }
  | decls decl ';'         { $2 : $1 }

vdecls                  :: { [Decl PName] }
  : decl                   { [$1] }
  | vdecls 'v;' decl       { $3 : $1 }
  | vdecls ';'  decl       { $3 : $1 }

decls_layout            :: { [Decl PName] }
  : 'v{' vdecls 'v}'       { $2 }
  | 'v{' 'v}'              { [] }

repl                    :: { ReplInput PName }
  : expr                   { ExprInput $1 }
  | let_decl               { LetInput $1 }

--------------------------------------------------------------------------------
-- if a then b else c : [10]


expr                             :: { Expr PName }
  : cexpr                           { $1 }
  | expr 'where' '{' '}'            { at ($1,$4) $ EWhere $1 []           }
  | expr 'where' '{' decls '}'      { at ($1,$5) $ EWhere $1 (reverse $4) }
  | expr 'where' 'v{' 'v}'          { at ($1,$2) $ EWhere $1 []           }
  | expr 'where' 'v{' vdecls 'v}'   { at ($1,$4) $ EWhere $1 (reverse $4) }
  | error                           {% expected "an expression" }

ifBranches                       :: { [(Expr PName, Expr PName)] }
  : ifBranch                        { [$1] }
  | ifBranches '|' ifBranch         { $3 : $1 }

ifBranch                         :: { (Expr PName, Expr PName) }
  : expr 'then' expr                { ($1, $3) }

cexpr                            :: { Expr PName }
  : sig_expr                        { $1 }
  | 'if' ifBranches 'else' cexpr    { at ($1,$4) $ mkIf (reverse $2) $4 }
  | '\\' apats '->' cexpr           { at ($1,$4) $ EFun (reverse $2) $4 }

sig_expr                         :: { Expr PName }
  : iexpr                           { $1 }
  | iexpr ':' type                  { at ($1,$3) $ ETyped $1 $3 }

iexpr                            :: { Expr PName }
  : expr10                          { $1 }
  | iexpr qop expr10                { binOp $1 $2 $3 }

expr10                           :: { Expr PName }
  : aexprs                          { mkEApp $1 }

  | '-' expr10 %prec NEG            { at ($1,$2) $ ENeg $2 }
  | '~' expr10                      { at ($1,$2) $ EComplement $2 }

qop                              :: { LPName }
  : op                              { $1 }
  | QOP                             { let Token (Op (Other ns i)) _ = thing $1
                                       in mkQual (mkModName ns) (mkInfix i) A.<$ $1 }

op                               :: { LPName }
  : pat_op                          { $1 }
  | '#'                             { Located $1 $ mkUnqual $ mkInfix "#" }

pat_op                           :: { LPName }
  : other_op                        { $1 }

    -- special cases for operators that are re-used elsewhere
  | '*'                             { Located $1 $ mkUnqual $ mkInfix "*" }
  | '+'                             { Located $1 $ mkUnqual $ mkInfix "+" }
  | '-'                             { Located $1 $ mkUnqual $ mkInfix "-" }
  | '~'                             { Located $1 $ mkUnqual $ mkInfix "~" }
  | '^^'                            { Located $1 $ mkUnqual $ mkInfix "^^" }


other_op                         :: { LPName }
  : OP                              { let Token (Op (Other [] str)) _ = thing $1
                                       in mkUnqual (mkInfix str) A.<$ $1 }


ops                     :: { [LPName] }
  : op                     { [$1] }
  | ops ',' op             { $3 : $1 }

aexprs                         :: { [Expr PName] }
  : aexpr                         { [$1]    }
  | aexprs aexpr                  { $2 : $1 }

aexpr                          :: { Expr PName }
  : no_sel_aexpr                  { $1 }
  | sel_expr                      { $1 }

no_sel_aexpr                   :: { Expr PName                             }
  : qname                         { at $1 $ EVar (thing $1)                }

  | NUM                           { at $1 $ numLit (tokenType (thing $1))  }
  | STRLIT                        { at $1 $ ELit $ ECString $ getStr $1    }
  | CHARLIT                       { at $1 $ ELit $ ECNum (getNum $1) CharLit }

  | '(' expr ')'                  { at ($1,$3) $ EParens $2                }
  | '(' tuple_exprs ')'           { at ($1,$3) $ ETuple (reverse $2)       }
  | '(' ')'                       { at ($1,$2) $ ETuple []                 }
  | '{' '}'                       { at ($1,$2) $ ERecord []                }
  | '{' rec_expr '}'              { at ($1,$3) $2                          }
  | '[' ']'                       { at ($1,$2) $ EList []                  }
  | '[' list_expr  ']'            { at ($1,$3) $2                          }
  | '`' tick_ty                   { at ($1,$2) $ ETypeVal $2               }

  | '(' qop ')'                   { at ($1,$3) $ EVar $ thing $2           }

  | '<|'            '|>'          {% mkPoly (rComb $1 $2) [] }
  | '<|' poly_terms '|>'          {% mkPoly (rComb $1 $3) $2 }


  -- | error                           {%^ customError "expr" }

sel_expr                       :: { Expr PName }
  : no_sel_aexpr '.' selector     { at ($1,$3) $ ESel $1 (thing $3)        }
  | sel_expr '.' selector         { at ($1,$3) $ ESel $1 (thing $3)        }


poly_terms                     :: { [(Bool, Integer)] }
  : poly_term                     { [$1] }
  | poly_terms '+' poly_term      { $3 : $1 }

poly_term                      :: { (Bool, Integer) }
  : NUM                           {% polyTerm (srcRange $1) (getNum $1) 0 }
  | 'x'                           {% polyTerm $1 1 1 }
  | 'x' '^^' NUM                  {% polyTerm (rComb $1 (srcRange $3))
                                                            1 (getNum $3) }

selector                       :: { Located Selector }
  : ident                         { fmap (`RecordSel` Nothing) $1 }
  | NUM                           {% mkTupleSel (srcRange $1) (getNum $1) }

tuple_exprs                    :: { [Expr PName] }
  : expr ',' expr                 { [ $3, $1] }
  | tuple_exprs ',' expr          { $3 : $1   }


rec_expr :: { Expr PName }
  : aexpr '|' field_exprs         { EUpd (Just $1) (reverse $3) }
  | '_'   '|' field_exprs         { EUpd Nothing   (reverse $3) }
  | field_exprs                   {% do { xs <- mapM ufToNamed $1;
                                          pure (ERecord (reverse xs)) } }

field_expr             :: { UpdField PName }
  : selector field_how expr     { UpdField $2 [$1] $3 }
  | sels field_how expr         { UpdField $2 $1 $3 }
  | sels apats field_how expr   { UpdField $3 $1 (EFun (reverse $2) $4) }
  | selector apats field_how expr   { UpdField $3 [$1] (EFun (reverse $2) $4) }

field_how :: { UpdHow }
  : '='                          { UpdSet }
  | '->'                         { UpdFun }

sels :: { [ Located Selector ] }
  : sel_expr                      {% selExprToSels $1 }

field_exprs                    :: { [UpdField PName] }
  : field_expr                    { [$1]    }
  | field_exprs ',' field_expr    { $3 : $1 }

list_expr                      :: { Expr PName }
  : expr '|' list_alts            { EComp $1 (reverse $3)    }
  | expr                          { EList [$1]               }
  | tuple_exprs                   { EList (reverse $1)       }

  {- The `expr` in the four productions that follow should be `type`.
     This, however, leads to ambiguity because the syntax for types and
     expressions overlaps and we need more than 1 look-ahead to resolve what
     is being parsed.  For this reason, we use `expr` temporarily and
     then convert it to the corresponding type in the AST. -}

  | expr          '..' expr       {% eFromTo $2 $1 Nothing   $3 }
  | expr ',' expr '..' expr       {% eFromTo $4 $1 (Just $3) $5 }

  | expr '...'                    { EInfFrom $1 Nothing         }
  | expr ',' expr '...'           { EInfFrom $1 (Just $3)       }


list_alts                      :: { [[Match PName]] }
  : matches                       { [ reverse $1 ] }
  | list_alts '|' matches         { reverse $3 : $1 }

matches                        :: { [Match PName] }
  : match                         { [$1] }
  | matches ',' match             { $3 : $1 }

match                          :: { Match PName }
  : pat '<-' expr                 { Match $1 $3 }


--------------------------------------------------------------------------------
pat                            :: { Pattern PName }
  : ipat ':' type                 { at ($1,$3) $ PTyped $1 $3 }
  | ipat                          { $1                        }

ipat                           :: { Pattern PName }
  : ipat '#' ipat                 { at ($1,$3) $ PSplit $1 $3 }
  | apat                          { $1                        }

apat                           :: { Pattern PName }
  : name                          { PVar $1                           }
  | '_'                           { at $1       $ PWild               }
  | '(' ')'                       { at ($1,$2) $ PTuple []            }
  | '(' pat ')'                   { at ($1,$3)   $2                   }
  | '(' tuple_pats ')'            { at ($1,$3) $ PTuple (reverse $2)  }
  | '[' ']'                       { at ($1,$2) $ PList []             }
  | '[' pat ']'                   { at ($1,$3) $ PList [$2]           }
  | '[' tuple_pats ']'            { at ($1,$3) $ PList (reverse $2)   }
  | '{' '}'                       { at ($1,$2) $ PRecord []           }
  | '{' field_pats '}'            { at ($1,$3) $ PRecord (reverse $2) }

tuple_pats                     :: { [Pattern PName] }
  : pat ',' pat                   { [$3, $1] }
  | tuple_pats ',' pat            { $3 : $1   }

field_pat                      :: { Named (Pattern PName) }
  : ident '=' pat                 { Named { name = $1, value = $3 } }

field_pats                     :: { [Named (Pattern PName)] }
  : field_pat                     { [$1]    }
  | field_pats ',' field_pat      { $3 : $1 }

--------------------------------------------------------------------------------

schema                         :: { Schema PName }
  : type                          { at $1 $ mkSchema [] [] $1      }
  | schema_vars type              { at ($1,$2) $ mkSchema (thing $1) [] $2 }
  | schema_quals type             { at ($1,$2) $ mkSchema [] (thing $1) $2 }
  | schema_vars schema_quals type { at ($1,$3) $ mkSchema (thing $1)
                                                          (thing $2) $3 }

schema_vars                    :: { Located [TParam PName] }
  : '{' '}'                       { Located (rComb $1 $2) [] }
  | '{' schema_params '}'         { Located (rComb $1 $3) (reverse $2) }

schema_quals                   :: { Located [Prop PName] }
  : type '=>'                     {% fmap (\x -> at (x,$2) x) (mkProp $1) }

kind                             :: { Located Kind      }
  : '#'                             { Located $1 KNum   }
  | '*'                             { Located $1 KType  }
  | kind '->' kind                  { combLoc KFun $1 $3 }

schema_param                   :: { TParam PName }
  : ident                         {% mkTParam $1 Nothing           }
  | ident ':' kind                {% mkTParam (at ($1,$3) $1) (Just (thing $3)) }

schema_params                    :: { [TParam PName] }
  : schema_param                    { [$1] }
  | schema_params ',' schema_param  { $3 : $1 }

tysyn_param                   :: { TParam PName }
  : ident                        {% mkTParam $1 Nothing }
  | '(' ident ':' kind ')'       {% mkTParam (at ($1,$5) $2) (Just (thing $4)) }

tysyn_params                  :: { [TParam PName]  }
  : tysyn_param                  { [$1]      }
  | tysyn_params tysyn_param     { $2 : $1   }

type                           :: { Type PName                                                 }
  : app_type '->' type            { at ($1,$3) $ TFun $1 $3                                    }
  | type op app_type              { at ($1,$3) $ TInfix $1 $2 defaultFixity $3 }
  | app_type                      { $1                                                         }

app_type                       :: { Type PName }
  -- : 'lg2'   atype                 { at ($1,$2) $ TApp TCLg2   [$2]    }
  -- | 'lengthFromThenTo' atype atype
  --                      atype      { at ($1,$4) $ TApp TCLenFromThenTo [$2,$3,$4] }
  -- | 'min'   atype atype           { at ($1,$3) $ TApp TCMin   [$2,$3] }
  -- | 'max'   atype atype           { at ($1,$3) $ TApp TCMax   [$2,$3] }

  : dimensions atype              { at ($1,$2) $ foldr TSeq $2 (reverse (thing $1)) }
  | qname atypes                  { at ($1,head $2)
                                     $ TUser (thing $1) (reverse $2) }
  | atype                         { $1                    }

atype                          :: { Type PName }
  : qname                         { at $1 $ TUser (thing $1) []        }
  | NUM                           { at $1 $ TNum  (getNum $1)          }
  | CHARLIT                       { at $1 $ TChar (toEnum $ fromInteger
                                                          $ getNum $1) }
  | '[' type ']'                  { at ($1,$3) $ TSeq $2 TBit          }
  | '(' type ')'                  { at ($1,$3) $ TParens $2            }
  | '(' ')'                       { at ($1,$2) $ TTuple []             }
  | '(' tuple_types ')'           { at ($1,$3) $ TTuple  (reverse $2)  }
  | '{' '}'                       { at ($1,$2) $ TRecord []            }
  | '{' field_types '}'           { at ($1,$3) $ TRecord (reverse $2)  }
  | '_'                           { at $1 TWild                        }

atypes                         :: { [ Type PName ] }
  : atype                         { [ $1 ]    }
  | atypes atype                  { $2 : $1   }

dimensions                     :: { Located [Type PName]  }
  : '[' type ']'                  { Located (rComb $1 $3) [ $2 ] }
  | dimensions '[' type ']'       { at ($1,$4) (fmap ($3 :) $1)  }

tuple_types                    :: { [Type PName] }
  : type ',' type                 { [ $3, $1] }
  | tuple_types ',' type          { $3 : $1   }

field_type                     :: { Named (Type PName) }
  : ident ':' type                { Named { name = $1, value = $3 } }

field_types                    :: { [Named (Type PName)] }
  : field_type                    { [$1]    }
  | field_types ',' field_type    { $3 : $1 }


ident              :: { Located Ident }
  : IDENT             { let Token (Ident _ str) _ = thing $1
                         in $1 { thing = mkIdent str } }
  | 'x'               { Located { srcRange = $1, thing = mkIdent "x" }}
  | 'private'         { Located { srcRange = $1, thing = mkIdent "private" } }
  | 'as'              { Located { srcRange = $1, thing = mkIdent "as" } }
  | 'hiding'          { Located { srcRange = $1, thing = mkIdent "hiding" } }


name               :: { LPName }
  : ident             { fmap mkUnqual $1 }


smodName                       :: { Located ModName }
  : ident                         { fmap (mkModName . (:[]) . identText) $1 }
  | QIDENT                        { let Token (Ident ns i) _ = thing $1
                                     in mkModName (ns ++ [i]) A.<$ $1 }


modName                        :: { Located ModName }
  : smodName                      { $1 }
  | '`' smodName                  { fmap paramInstModName $2 }


qname                          :: { Located PName }
  : name                          { $1 }
  | QIDENT                        { let Token (Ident ns i) _ = thing $1
                                     in mkQual (mkModName ns) (mkIdent i) A.<$ $1 }

help_name                      :: { Located PName    }
  : qname                         { $1               }
  | qop                           { $1               }
  | '(' qop ')'                   { $2               }

{- The types that can come after a back-tick: either a type demotion,
or an explicit type application.  Explicit type applications are converted
to records, which cannot be demoted. -}
tick_ty                        :: { Type PName }
  : qname                         { at $1 $ TUser (thing $1) []      }
  | NUM                           { at $1 $ TNum  (getNum $1)          }
  | '(' type ')'                  {% validDemotedType (rComb $1 $3) $2 }
  | '{' '}'                       { at ($1,$2) (TRecord [])            }
  | '{' field_ty_vals '}'         { at ($1,$3) (TRecord (reverse $2))  }
  | '{' type '}'                  { anonRecord (getLoc ($1,$3)) [$2]   }
  | '{' tuple_types '}'           { anonRecord (getLoc ($1,$3)) (reverse $2) }

-- This for explicit type applications (e.g., f ` { front = 3 })
field_ty_val                   :: { Named (Type PName)              }
  : ident '=' type                { Named { name = $1, value = $3 } }

field_ty_vals                  :: { [Named (Type PName)] }
  : field_ty_val                    { [$1]       }
  | field_ty_vals ',' field_ty_val  { $3 : $1    }




{

parseModName :: String -> Maybe ModName
parseModName txt =
  case parseString defaultConfig { cfgModuleScope = False } modName txt of
    Right a -> Just (thing a)
    Left _  -> Nothing

parseHelpName :: String -> Maybe PName
parseHelpName txt =
  case parseString defaultConfig { cfgModuleScope = False } helpName txt of
    Right a -> Just (thing a)
    Left _  -> Nothing

addImplicitIncludes :: Config -> Program PName -> Program PName
addImplicitIncludes cfg (Program ds) =
  Program $ map path (cfgAutoInclude cfg) ++ ds
  where path p = Include Located { srcRange = rng, thing = p }
        rng    = Range { source = cfgSource cfg, from = start, to = start }


parseProgramWith :: Config -> Text -> Either ParseError (Program PName)
parseProgramWith cfg s = case res s of
                          Left err -> Left err
                          Right a  -> Right (addImplicitIncludes cfg a)
  where
  res = parse cfg $ case cfgLayout cfg of
                      Layout   -> programLayout
                      NoLayout -> program

parseModule :: Config -> Text -> Either ParseError (Module PName)
parseModule cfg = parse cfg { cfgModuleScope = True } vmodule

parseProgram :: Layout -> Text -> Either ParseError (Program PName)
parseProgram l = parseProgramWith defaultConfig { cfgLayout = l }

parseExprWith :: Config -> Text -> Either ParseError (Expr PName)
parseExprWith cfg = parse cfg { cfgModuleScope = False } expr

parseExpr :: Text -> Either ParseError (Expr PName)
parseExpr = parseExprWith defaultConfig

parseDeclWith :: Config -> Text -> Either ParseError (Decl PName)
parseDeclWith cfg = parse cfg { cfgModuleScope = False } decl

parseDecl :: Text -> Either ParseError (Decl PName)
parseDecl = parseDeclWith defaultConfig

parseDeclsWith :: Config -> Text -> Either ParseError [Decl PName]
parseDeclsWith cfg = parse cfg { cfgModuleScope = ms } decls'
  where (ms, decls') = case cfgLayout cfg of
                         Layout   -> (True, declsLayout)
                         NoLayout -> (False, decls)

parseDecls :: Text -> Either ParseError [Decl PName]
parseDecls = parseDeclsWith defaultConfig

parseLetDeclWith :: Config -> Text -> Either ParseError (Decl PName)
parseLetDeclWith cfg = parse cfg { cfgModuleScope = False } letDecl

parseLetDecl :: Text -> Either ParseError (Decl PName)
parseLetDecl = parseLetDeclWith defaultConfig

parseReplWith :: Config -> Text -> Either ParseError (ReplInput PName)
parseReplWith cfg = parse cfg { cfgModuleScope = False } repl

parseRepl :: Text -> Either ParseError (ReplInput PName)
parseRepl = parseReplWith defaultConfig

parseSchemaWith :: Config -> Text -> Either ParseError (Schema PName)
parseSchemaWith cfg = parse cfg { cfgModuleScope = False } schema

parseSchema :: Text -> Either ParseError (Schema PName)
parseSchema = parseSchemaWith defaultConfig

-- vim: ft=haskell
}

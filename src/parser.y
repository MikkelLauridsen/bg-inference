{

module Parser 
( parse
) where

import Lexer
import PiCalculus

}

%name parse
%tokentype { Token }
%monad { Alex }
%lexer { tokenize } { EOFT }
%errorhandlertype explist
%error { parseError }

%token
    new          { NewT }         -- new
    succ         { SuccT }        -- succ
    zero         { ZeroT }        -- zero
    in           { InT  }         -- in
    var          { VarT _ }       -- [a-z]+[0-9]*
    '!'          { RepT }         -- *
    '.'          { DotT }         -- .
    '?'          { QuestionT }    -- ?
    '!'          { ExclamationT } -- !
    '('          { ParenLT }      -- (
    ')'          { ParenRT }      -- )
    '|'          { SepaT }        -- |
    ','          { CommaT }       -- ,
    nat          { NatT _ }       -- [0-9]+
    tick         { TickT }        -- tick
    match        { MatchT }       -- match
    '{'          { CurlyLT }      -- {
    '}'          { CurlyRT }      -- }
    ';'          { SemiT }        -- ;
    '->'         { ArrowT }       -- ->

%%

Proc : AProc          { $1 }
     | AProc '|' Proc { $1 :|: $2 }

AProc : tick '.' AProc                                                  { TickP $3 }
      | '!' var '?' '(' Vars ')'                                        { RepInputP (getVar $2) $5 NilP }
      | '!' var '?' '(' Vars ')' '.' '(' Proc ')'                       { RepInputP (getVar $2) $5 $9 }  
      | var '?' '(' Vars ')'                                            { InputP (getVar $1) $4 NilP }
      | var '?' '(' Vars ')' '.' '(' Proc ')'                           { InputP (getVar $1) $4 $8 }  
      | var '!' '(' Exps ')'                                            { OutputP (getVar $1) $4 }
      | new var in Proc                                                 { RestrictP (getVar $2) stypePlaceholder $4 }
      | match Exp '{' zero '->' Proc ';' succ '(' var ')' '->' Proc '}' { MatchNatP $2 $6 (getVar $10) $13 }

Exp : zero             { ZeroE }
    | succ '(' Exp ')' { SuccE $3 }
    | var              { VarE (getVar $1) }
    | nat              { (unfoldNat (getNat $1)) }

Vars :         { [] }
     | VarList { $1 }

Exps :         { [] }
     | ExpList { $1 }

VarList : var             { [getVar $1] }
        | var ',' VarList { getVar $1 : $3 }

ExpList : Exp             { [$1] }
        | Exp ',' ExpList { $1 : $3 }

{

    -- TODO: write helper functions

    stypePlaceholder = STVar TypeVar -1 -- todo 
}
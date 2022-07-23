{

module Parser 
( parse
) where

import Lexer
import PiCalculus
import Types

}

%name parse
%tokentype { Token }
%monad { Maybe }
%errorhandlertype explist
%error { parseError }

%token
    new          { NewT }         -- new
    succ         { SuccT }        -- succ
    zero         { ZeroT }        -- zero
    in           { InT  }         -- in
    var          { VarT $$ }      -- [a-z]+[0-9]*
    '*'          { RepT }         -- *
    '.'          { DotT }         -- .
    '?'          { QuestionT }    -- ?
    '!'          { ExclamationT } -- !
    '('          { ParenLT }      -- (
    ')'          { ParenRT }      -- )
    '|'          { SepaT }        -- |
    ','          { CommaT }       -- ,
    nat          { NatT $$ }       -- [0-9]+
    tick         { TickT }        -- tick
    match        { MatchT }       -- match
    '{'          { CurlyLT }      -- {
    '}'          { CurlyRT }      -- }
    ';'          { SemiT }        -- ;
    '->'         { ArrowT }       -- ->

%%

Proc : AProc          { $1 }
     | AProc '|' Proc { $1 :|: $3 }

AProc : tick '.' AProc                                                  { TickP $3 }
      | '!' var '?' '(' Vars ')'                                        { RepInputP $2 $5 NilP }
      | '!' var '?' '(' Vars ')' '.' '(' Proc ')'                       { RepInputP $2 $5 $9 }  
      | var '?' '(' Vars ')'                                            { InputP $1 $4 NilP }
      | var '?' '(' Vars ')' '.' '(' Proc ')'                           { InputP $1 $4 $8 }  
      | var '!' '(' Exps ')'                                            { OutputP $1 $4 }
      | new var in Proc                                                 { RestrictP $2 stypePlaceholder $4 }
      | match Exp '{' zero '->' Proc ';' succ '(' var ')' '->' Proc '}' { MatchNatP $2 $6 $10 $13 }

Exp : zero             { ZeroE }
    | succ '(' Exp ')' { SuccE $3 }
    | var              { VarE $1 }
    | nat              { (unfoldNat $1) }

Vars :         { [] }
     | VarList { $1 }

Exps :         { [] }
     | ExpList { $1 }

VarList : var             { [$1] }
        | var ',' VarList { $1 : $3 }

ExpList : Exp             { [$1] }
        | Exp ',' ExpList { $1 : $3 }

{

stypePlaceholder = STVar (-1) -- todo 

unfoldNat :: Int -> Exp
unfoldNat n 
    | n <= 0 = ZeroE
    | otherwise = SuccE $ unfoldNat (n - 1)


parseError :: ([Token], [String]) -> Maybe a
parseError _ = Nothing -- TODO


}
{

module Parser 
( parse
, addFreshTypeVars
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
    nil          { NilT }         -- nil
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

AProc : nil                                                             { NilP }
      | tick '.' AProc                                                  { TickP $3 }
      | tick                                                            { TickP NilP }
      | '*' var '?' '(' Vars ')'                                        { RepInputP $2 $5 NilP }
      | '*' var '?' '(' Vars ')' '.' '(' Proc ')'                       { RepInputP $2 $5 $9 }  
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

stypePlaceholder = STVar (-1)

unfoldNat :: Int -> Exp
unfoldNat n 
    | n <= 0 = ZeroE
    | otherwise = SuccE $ unfoldNat (n - 1)


parseError :: ([Token], [String]) -> Maybe a
parseError _ = Nothing -- TODO


addFreshTypeVars :: Proc -> Proc
addFreshTypeVars p = fst $ aux 0 p
    where
        aux :: Int -> Proc -> (Proc, Int)
        aux i (p :|: q) = (p' :|: q', k)
            where
                (p', j) = aux i p
                (q', k) = aux j q
        
        aux i (InputP a vs p) = (InputP a vs p', j)
            where
                (p', j) = aux i p

        aux i (RepInputP a vs p) = (RepInputP a vs p', j)
            where
                (p', j) = aux i p

        aux i (RestrictP a _ p) = (RestrictP a (STVar i) p', j)
            where
                (p', j) = aux (i + 1) p

        aux i (MatchNatP e p x q) = (MatchNatP e p' x q', k)
            where
                (p', j) = aux i p
                (q', k) = aux j q

        aux i p = (p, i)

}
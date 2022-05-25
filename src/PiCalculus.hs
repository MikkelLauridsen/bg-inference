module PiCalculus
  ( Var,
    Exp (..),
    Proc (..),
    natExp,
    nTick,
  )
where

import Types

type Var = String

natExp :: Int -> Exp
natExp 0 = ZeroE
natExp n = SuccE (natExp (n - 1))

nTick :: Int -> Proc -> Proc
nTick 0 p = p
nTick n p = nTick (n - 1) (TickP p)

data Exp
  = ZeroE
  | SuccE Exp
  | VarE Var
  deriving (Show)

data Proc
  = NilP
  | TickP Proc
  | Proc :|: Proc
  | InputP Var [Var] Proc
  | OutputP Var [Exp]
  | RepInputP Var [Var] Proc
  | RestrictP Var SimpleType Proc
  | MatchNatP Exp Proc Var Proc
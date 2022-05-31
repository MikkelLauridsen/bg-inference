module PiCalculus
  ( Var,
    Exp (..),
    Proc (..),
    natExp,
    nTick,
    applySTVSubst
  )
where

import Types
import Data.Map as Map

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
  deriving (Show)


applySTVSubst :: SimpleTypeSubstitution -> Proc -> Proc
applySTVSubst subst (TickP p) = TickP $ applySTVSubst subst p
applySTVSubst subst (p :|: q) = applySTVSubst subst p :|: applySTVSubst subst q
applySTVSubst subst (InputP a vs p) = InputP a vs $ applySTVSubst subst p
applySTVSubst subst (RepInputP a vs p) = RepInputP a vs $ applySTVSubst subst p
applySTVSubst subst (RestrictP a st p) = RestrictP a (aux st) $ applySTVSubst subst p
  where
    aux st'@(STVar beta) = Map.findWithDefault st' beta subst 
    aux STNat = STNat
    aux (STChannel sts) = STChannel $ Prelude.map aux sts
    aux (STServ is sts) = STServ is $ Prelude.map aux sts

applySTVSubst subst (MatchNatP e p x q) = MatchNatP e (applySTVSubst subst p) x (applySTVSubst subst q)
applySTVSubst _ p = p


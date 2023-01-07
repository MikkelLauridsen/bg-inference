module PiCalculus
  ( Var,
    Exp (..),
    Proc (..),
    AnnotatedProc (..),
    natExp,
    nTick,
    applySTVSubst
  )
where

import Types
import Data.Map as Map
import Data.List(intercalate)

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


data AnnotatedProc
  = NilAP
  | TickAP AnnotatedProc
  | AnnotatedProc :||: AnnotatedProc
  | InputAP Var [(Var, Type)] AnnotatedProc
  | OutputAP Var [Exp]
  | RepInputAP Var [(Var, Type)] AnnotatedProc
  | RestrictAP Var Type AnnotatedProc
  | MatchNatAP Exp AnnotatedProc Var Type AnnotatedProc

instance Show Exp where
  show ZeroE = "0"
  show (VarE v) = v
  show e@(SuccE _) = show n
    where
      n = countSuccs e

      countSuccs ZeroE = 0
      countSuccs (SuccE e') = 1 + countSuccs e'


instance Show AnnotatedProc where
  show NilAP = "\\texttt{nil}"
  show (TickAP ap) = "\\texttt{tick}." ++ show ap
  show (ap1 :||: ap2) = "\\left(" ++ show ap1 ++ "\\mid" ++ show ap2 ++ "\\right)"
  show (InputAP a vts ap) = "\\textit{" ++ a ++ "}?\\!\\left(" ++ intercalate ", " (Prelude.map (\(v, t) -> v ++ " :: " ++ show t) vts) ++ "\\right)\\!.\\!" ++ show ap 
  show (OutputAP a es) = "\\textit{" ++ a ++ "}!\\!\\left(" ++ intercalate ", " (Prelude.map show es) ++ "\\right)"
  show (RepInputAP a vts ap) = "*\\textit{" ++ a ++ "}?\\!\\left(" ++ intercalate ", " (Prelude.map (\(v, t) -> v ++ " :: " ++ show t) vts) ++ "\\right)\\!.\\!" ++ show ap 
  show (RestrictAP a t ap) = "\\texttt{new}\\;\\textit{" ++ a ++ "} :: " ++ show t ++ "\\;\\texttt{in}\\; " ++ show ap
  show (MatchNatAP e ap1 x t ap2) = "\\texttt{match}\\; " ++ show e ++ " \\{ " ++ "\\texttt{zero} \\rightarrow " ++ show ap1 ++ "; \\texttt{succ}\\!\\left(\\textit{" ++ x ++ "} :: " ++ show t ++ "\\right) \\rightarrow " ++ show ap2 ++ " \\}"


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


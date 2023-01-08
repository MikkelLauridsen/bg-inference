module Types
  ( SimpleType (..),
    Type (..),
    Index,
    CapabVar (..),
    IndexVar,
    TypeVar,
    UseCapabilityType (..),
    UseCapability (..),
    SimpleTypeSubstitution,
    typeSubst,
    applyISubstType,
    applyUseValuation,
    UseValuation
  )
where

import Data.List (intercalate)
import Data.Map
import qualified Data.Map as Map
import Data.Maybe
import Data.Set as Set
import Index


type UseValuation = Map CapabVar (Set UseCapabilityType)

newtype CapabVar = CapabVar Int deriving (Eq, Ord)

type TypeVar = Int

type SimpleTypeSubstitution = Map TypeVar SimpleType

data UseCapabilityType = UCIn | UCOut deriving (Eq, Ord)

data UseCapability = UCVar CapabVar | UCSet (Set UseCapabilityType) deriving (Eq, Ord)

data SimpleType
  = STVar TypeVar
  | STNat
  | STChannel [SimpleType]
  | STServ (Set IndexVar) [SimpleType]
  deriving (Show, Eq)

data Type
  = TNat Index Index
  | TChannel UseCapability Index [Type]
  | TServ Index (Set IndexVar) UseCapability Index [Type]
  | TInvar (Set IndexVar) UseCapability Index [Type]
  | TVar TypeVar -- for bound variables that are not used by a process
  deriving (Ord, Eq)

substituteSimpleTypes :: SimpleType -> SimpleTypeSubstitution -> SimpleType
substituteSimpleTypes (STVar v) sub = fromMaybe (STVar v) (Map.lookup v sub)
substituteSimpleTypes STNat _ = STNat
substituteSimpleTypes (STChannel ts) sub = STChannel (Prelude.map (`substituteSimpleTypes` sub) ts)
substituteSimpleTypes (STServ i ts) sub = STServ i (Prelude.map (`substituteSimpleTypes` sub) ts)

instance Show CapabVar where
  show (CapabVar n) = "\\gamma_{" ++ show n ++ "}"

instance Show UseCapabilityType where
  show UCIn = "\\texttt{in}"
  show UCOut = "\\texttt{out}"

instance Show UseCapability where
  show (UCVar gamma) = show gamma
  show (UCSet sigma) = "\\{" ++ intercalate ", " (Prelude.map show (Set.toList sigma)) ++ "\\}"

instance Show Type where
  show (TNat ix jx) = "\\texttt{Nat}[" ++ show ix ++ ", " ++ show jx ++ "]"
  show (TChannel sigma ix ts) = "\\texttt{ch}^{" ++ show sigma ++ "}_{" ++ show ix ++ "}(" ++ intercalate ", " (Prelude.map show ts) ++ ")"
  show (TServ ix is sigma kx ts) = "\\forall_{" ++ show ix ++ "}{" ++ intercalate ", " (Prelude.map show (Set.toList is)) ++ "}.\\texttt{serv}^{" ++ show sigma ++ "}_{" ++ show kx ++ "}(" ++ intercalate ", " (Prelude.map show ts) ++ ")"
  show (TInvar is sigma kx ts) = "\\forall{" ++ intercalate ", " (Prelude.map show (Set.toList is)) ++ "}.\\texttt{invar}^{" ++ show sigma ++ "}_{" ++ show kx ++ "}(" ++ intercalate ", " (Prelude.map show ts) ++ ")"
  show (TVar b) = "\\beta_{" ++ show b ++ "}"


typeSubst :: Map IndexVar Index -> Type -> Type
typeSubst subst (TNat ix jx) = TNat (indexSubst ix subst) (indexSubst jx subst)
typeSubst subst (TChannel sigma ix ts) = TChannel sigma (indexSubst ix subst) $ Prelude.map (typeSubst subst) ts
typeSubst subst (TServ ix is sigma kx ts) = TServ (indexSubst ix subst) is sigma (indexSubst kx subst') $ Prelude.map (typeSubst subst') ts
  where
    subst' = Set.foldr Map.delete subst is

applyISubstType :: Map CoeffVar Integer -> Type -> Type
applyISubstType substI (TNat ix jx) = TNat (applyISubst substI ix) (applyISubst substI jx)
applyISubstType substI (TChannel sigma ix ts) = TChannel sigma (applyISubst substI ix) $ Prelude.map (applyISubstType substI) ts
applyISubstType substI (TServ ix is sigma kx ts) = TServ (applyISubst substI ix) is sigma (applyISubst substI kx) $ Prelude.map (applyISubstType substI) ts


applyUseValuation :: UseValuation -> Type -> Type
applyUseValuation _ t@(TNat _ _) = t
applyUseValuation f (TChannel (UCVar gamma) ix ts) | gamma `Map.member` f = TChannel (UCSet $ f ! gamma) ix $ Prelude.map (applyUseValuation f) ts
applyUseValuation f (TChannel sigma ix ts) = TChannel sigma ix $ Prelude.map (applyUseValuation f) ts
applyUseValuation f (TServ ix is (UCVar gamma) kx ts) | gamma `Map.member` f = TServ ix is (UCSet $ f ! gamma) kx $ Prelude.map (applyUseValuation f) ts
applyUseValuation f (TServ ix is sigma kx ts) = TServ ix is sigma kx $ Prelude.map (applyUseValuation f) ts
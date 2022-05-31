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
  )
where

import Data.List (intercalate)
import Data.Map
import qualified Data.Map as Map
import Data.Maybe
import Data.Set as Set
import Index

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
  deriving (Ord, Eq)

substituteSimpleTypes :: SimpleType -> SimpleTypeSubstitution -> SimpleType
substituteSimpleTypes (STVar v) sub = fromMaybe (STVar v) (Map.lookup v sub)
substituteSimpleTypes STNat _ = STNat
substituteSimpleTypes (STChannel ts) sub = STChannel (Prelude.map (`substituteSimpleTypes` sub) ts)
substituteSimpleTypes (STServ i ts) sub = STServ i (Prelude.map (`substituteSimpleTypes` sub) ts)

instance Show CapabVar where
  show (CapabVar n) = 'g' : show n

instance Show UseCapabilityType where
  show UCIn = "In"
  show UCOut = "Out"

instance Show UseCapability where
  show (UCVar gamma) = show gamma
  show (UCSet sigma) = "{" ++ intercalate ", " (Prelude.map show (Set.toList sigma)) ++ "}"

instance Show Type where
  show (TNat ix jx) = "Nat[" ++ show ix ++ ", " ++ show jx ++ "]"
  show (TChannel sigma ix ts) = "ch^" ++ show sigma ++ "_" ++ show ix ++ "(" ++ intercalate ", " (Prelude.map show ts) ++ ")"
  show (TServ ix is sigma kx ts) = "\\forall_" ++ show ix ++ "{" ++ intercalate ", " (Prelude.map show (Set.toList is)) ++ "}.serv^" ++ show sigma ++ "_" ++ show kx ++ "(" ++ intercalate ", " (Prelude.map show ts) ++ ")"

typeSubst :: Map IndexVar Index -> Type -> Type
typeSubst subst (TNat ix jx) = TNat (indexSubst ix subst) (indexSubst jx subst)
typeSubst subst (TChannel sigma ix ts) = TChannel sigma (indexSubst ix subst) $ Prelude.map (typeSubst subst) ts
typeSubst subst (TServ ix is sigma kx ts) = TServ (indexSubst ix subst) is sigma (indexSubst kx subst') $ Prelude.map (typeSubst subst') ts
  where
    subst' = Set.foldr Map.delete subst is
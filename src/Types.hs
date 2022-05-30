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
  )
where

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
  | STServ (Set IndexVar) [SimpleType] deriving (Show, Eq)

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
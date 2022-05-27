module Types
  ( SimpleType (..),
    Type (..),
    Index,
    IndexConstraintEnv,
    CapabilityVar,
    IndexVar,
    TypeVar,
    UseCapability (..),
    Coefficient (..),
    SimpleTypeSubstitution,
  )
where

import Data.Map
import qualified Data.Map as Map
import Data.Maybe
import Data.Set

type Index = Int -- TODO change

type IndexConstraint = (Index, Index) -- TODO change

type IndexConstraintEnv = (Set IndexVar, Set IndexConstraint)

type CapabilityVar = Int

type IndexVar = Int

type TypeVar = Int

type CoefficientVar = Int

type SimpleTypeSubstitution = Map TypeVar SimpleType

data UseCapability = UCVar CapabilityVar | UCIn | UCOut | UCInOut

data SimpleType = STVar TypeVar | STNat | STChannel [SimpleType] | STServ [IndexVar] [SimpleType] deriving (Show, Eq)

data Type = TNat Index Index | TChannel [Type] UseCapability Index | TServ Index [IndexVar] [Type] UseCapability Index

data Coefficient = COEVar CoefficientVar | COENumeral Double | COEAdd Coefficient Coefficient | COEMul Coefficient Coefficient

unionUCapability :: UseCapability -> UseCapability -> UseCapability
unionUCapability (UCVar _) _ = error "unionIO: impossible"
unionUCapability _ (UCVar _) = error "unionIO: impossible"
unionUCapability UCIn UCIn = UCIn
unionUCapability UCOut UCOut = UCOut
unionUCapability UCOut UCIn = UCInOut
unionUCapability UCIn UCOut = UCInOut
unionUCapability UCInOut _ = UCInOut
unionUCapability _ UCInOut = UCInOut

substituteSimpleTypes :: SimpleType -> SimpleTypeSubstitution -> SimpleType
substituteSimpleTypes (STVar v) sub = fromMaybe (STVar v) (Map.lookup v sub)
substituteSimpleTypes STNat _ = STNat
substituteSimpleTypes (STChannel ts) sub = STChannel (Prelude.map (`substituteSimpleTypes` sub) ts)
substituteSimpleTypes (STServ i ts) sub = STServ i (Prelude.map (`substituteSimpleTypes` sub) ts)
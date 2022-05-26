module Types
  ( SimpleType (..),
    Type (..),
    Index,
    IndexConstraintEnv,
    CapabilityVar,
    IndexVar,
    TypeVar,
    IOCapability (..),
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

data IOCapability = IOCVar CapabilityVar | IOCIn | IOCOut | IOCInOut

data SimpleType = STVar TypeVar | STNat | STChannel [SimpleType] | STServ [IndexVar] [SimpleType] deriving (Show, Eq)

data Type = TNat Index Index | TChannel [Type] IOCapability Index | TServ Index [IndexVar] [Type] IOCapability Index

data Coefficient = COEVar CoefficientVar | COENumeral Double | COEAdd Coefficient Coefficient | COEMul Coefficient Coefficient

unionIO :: IOCapability -> IOCapability -> IOCapability
unionIO (IOCVar _) _ = error "unionIO: impossible"
unionIO _ (IOCVar _) = error "unionIO: impossible"
unionIO IOCIn IOCIn = IOCIn
unionIO IOCOut IOCOut = IOCOut
unionIO IOCOut IOCIn = IOCInOut
unionIO IOCIn IOCOut = IOCInOut
unionIO IOCInOut _ = IOCInOut
unionIO _ IOCInOut = IOCInOut

substituteSimpleTypes :: SimpleType -> SimpleTypeSubstitution -> SimpleType
substituteSimpleTypes (STVar v) sub = fromMaybe (STVar v) (Map.lookup v sub)
substituteSimpleTypes STNat _ = STNat
substituteSimpleTypes (STChannel ts) sub = STChannel (Prelude.map (`substituteSimpleTypes` sub) ts)
substituteSimpleTypes (STServ i ts) sub = STServ i (Prelude.map (`substituteSimpleTypes` sub) ts)
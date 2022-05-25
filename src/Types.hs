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
  )
where

import Data.Set

type Index = Int -- TODO change

type IndexConstraint = (Index, Index) -- TODO change

type IndexConstraintEnv = (Set IndexVar, Set IndexConstraint)

type CapabilityVar = Int

type IndexVar = Int

type TypeVar = Int

type CoefficientVar = Int

data IOCapability = IOCVar CapabilityVar | IOCIn | IOCOut | IOCInOut

data SimpleType = STVar TypeVar | STNat | STChannel [SimpleType] | STServ [IndexVar] [SimpleType]

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
module Constraints
  ( Constraint (..),
    SimpleTypeConstraint (..),
    IOCapabilityConstraint (..),
    TypeConstraint (..),
    IndexConstraint (..),
    CoefficientConstraint (..),
  )
where

import Types

data Constraint
  = CSSimple SimpleTypeConstraint
  | CSCapability IOCapabilityConstraint
  | CSType TypeConstraint
  | CSIndex IndexConstraint
  | CSCoefficient CoefficientConstraint
  | CSFalse

data SimpleTypeConstraint
  = STCSEqual SimpleType SimpleType
  | STCSChannelServer SimpleType [SimpleType]

data IOCapabilityConstraint
  = IOSCEqual IOCapability IOCapability
  | IOCSSubset IOCapability IOCapability

data TypeConstraint
  = TCSEqual Type Type
  | TCSInvariant IndexConstraintEnv Type
  | TCSSubtype IndexConstraintEnv Type Type

data IndexConstraint
  = ICSEqual Index Index
  | ICSLessEq IndexConstraintEnv Index Index

data CoefficientConstraint
  = CCSEqual Coefficient Coefficient
  | CCSLessEq IndexConstraintEnv Coefficient Coefficient

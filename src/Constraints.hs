module Constraints
  ( 
    SimpleTypeConstraint (..),
    TypeConstraint (..),
    UseConstraint (..),
    CoefficientConstraint (..),
    UseCapabilityConstraint (..),
  )
where

import Types

data SimpleTypeConstraint -- c_b, STSC = Simple Type Constraint
  = STCSEqual SimpleType SimpleType
  | STCSChannelServer SimpleType [SimpleType]
  | STCSFalse

data TypeConstraint -- c_T, TCS = Type constraint
  = TCSEqual Type Type
  | TCSEqualIndex Index Index
  | TCSInvariant IndexConstraintEnv Type
  | TCSConditionalSubsumption IndexConstraintEnv Type Type
  | TCSUse UseConstraint

data UseConstraint --c_IO, USC = Use constraint
  = UCSConditionalInequality [UseCapabilityConstraint] IndexConstraintEnv Index Index
  | USCConditional [UseCapabilityConstraint] UseCapabilityConstraint
  | USCCoefficient CoefficientConstraint

data CoefficientConstraint -- c_a, CCS = Coefficient constraint
  = CCSEqual Coefficient Coefficient
  | CCSLessEq IndexConstraintEnv Index Index
  | CCSFalse

data UseCapabilityConstraint -- c_gamma, UCCS = Use capability constraint
  = UCCSSubset UseCapability UseCapability
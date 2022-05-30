module Constraints
  ( SimpleTypeConstraint (..),
    TypeConstraint (..),
    UseConstraint (..),
    IndexConstraint (..),
    UseCapabilityConstraint (..),
  )
where

import Index
import Types

data SimpleTypeConstraint -- c_b, STSC = Simple Type Constraint
  = STCSEqual SimpleType SimpleType
  | STCSChannelServer SimpleType [SimpleType]

data TypeConstraint -- c_T, TCS = Type constraint
  = TCSEqual Type Type
  | TCSInvariant IndexTypeConstraintEnv Type
  | TCSConditionalSubsumption IndexTypeConstraintEnv Type Type
  | TCSUse UseConstraint

data UseConstraint --c_IO, USC = Use constraint
  = UCSConditionalInequality [UseCapabilityConstraint] IndexTypeConstraintEnv Index Index
  | USCConditional [UseCapabilityConstraint] UseCapabilityConstraint
  | USCCoefficient IndexConstraint

data IndexConstraint -- c_I, ICS = Index constraint
  = ICSIndexEqual Index Index
  | ICSLessEq IndexTypeConstraintEnv Index Index
  | ICSFalse

data UseCapabilityConstraint -- c_gamma, UCCS = Use capability constraint
  = UCCSSubset UseCapability UseCapability
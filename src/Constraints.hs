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
import Data.Set as Set

data SimpleTypeConstraint -- c_b, STSC = Simple Type Constraint
  = STCSEqual SimpleType SimpleType
  | STCSChannelServer SimpleType [SimpleType]

data TypeConstraint -- c_T, TCS = Type constraint
  = TCSEqual Type Type
  | TCSEqualIndex Index Index
  | TCSInvariant IndexVarConstraintEnv Type
  | TCSConditionalSubsumption [UseCapabilityConstraint] IndexVarConstraintEnv Type Type
  | TCSUse UseConstraint
  deriving (Ord, Eq)

data UseConstraint --c_IO, USC = Use constraint
  = USCConditionalInequality [UseCapabilityConstraint] IndexVarConstraintEnv Index Index
  | USCConditional [UseCapabilityConstraint] UseCapabilityConstraint
  | USCIndex IndexConstraint
  deriving (Ord, Eq)

data IndexConstraint -- c_a, CCS = Coefficient constraint
  = ICSEqual Index Index
  | ICSLessEq IndexVarConstraintEnv Index Index
  | ICSFalse
  deriving (Ord, Eq)

data UseCapabilityConstraint -- c_gamma, UCCS = Use capability constraint
  = UCCSSubset UseCapability UseCapability
  deriving (Ord, Eq)
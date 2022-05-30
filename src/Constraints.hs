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
import Data.List(intercalate)

data SimpleTypeConstraint -- c_b, STSC = Simple Type Constraint
  = STCSEqual SimpleType SimpleType
  | STCSChannelServer SimpleType [SimpleType]

data TypeConstraint -- c_T, TCS = Type constraint
  = TCSEqual Type Type
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


instance Show TypeConstraint where

  show (TCSEqual t s) = show t ++ "~" ++ show s
  show (TCSInvariant env t) = showEnv env ++ "|= inv(" ++ show t ++ ")"
  show (TCSConditionalSubsumption uccs env t s) = "(" ++ intercalate ", " (Prelude.map show uccs) ++  ") ==> (" ++ showEnv env ++ "|= " ++ show t ++ " \\sqsubseteq " ++ show s ++ ")"
  show (TCSUse cs) = show cs


instance Show UseConstraint where

  show (USCConditionalInequality uccs env ix jx) = "(" ++ intercalate ", " (Prelude.map show uccs) ++  ") ==> (" ++ showEnv env ++ "|= " ++ show ix ++ " <= " ++ show jx ++ ")"
  show (USCConditional uccs ucc) = "(" ++ intercalate ", " (Prelude.map show uccs) ++  ") ==> " ++ show ucc
  show (USCIndex cs) = show cs


instance Show IndexConstraint where

  show (ICSEqual ix jx) = show ix ++ "~" ++ show jx
  show (ICSLessEq env ix jx) = showEnv env ++ "|= " ++ show ix ++ " <= " ++ show jx
  show ICSFalse = "FALSE"


instance Show UseCapabilityConstraint where

  show (UCCSSubset sigma sigma') = show sigma ++ " \\subseteq " ++ show sigma'


showEnv (vphi, phi) = "{" ++ intercalate ", " (Prelude.map show $ Set.toList vphi) ++ "};{" ++ intercalate ", " (Prelude.map show $ Set.toList phi) ++ "}"
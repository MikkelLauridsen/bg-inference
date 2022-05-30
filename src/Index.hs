module Index
  ( CoefficientVar,
    IndexVar,
    Coefficient (..),
    Index,
    IndexTypeConstraint (..),
    IndexTypeConstraintEnv,
  )
where

import Data.Map
import Data.Set

type CoefficientVar = Int

type IndexVar = Int

data Coefficient = COEVar CoefficientVar | COENumeral Double | COEAdd Coefficient Coefficient | COEMul Coefficient Coefficient

type Index = (Map IndexVar Coefficient, Coefficient)

data IndexTypeConstraint = ITCSLessEq Index Index

type IndexTypeConstraintEnv = (Set IndexVar, Set IndexTypeConstraint)

module Index
  ( CoeffVar (..),
    IndexVar (..),
    Coefficient (..),
    Index,
    IndexVarConstraint (..),
    IndexVarConstraintEnv,
  )
where

import Data.Map as Map
import Data.Set as Set

newtype CoeffVar = CoeffVar Int deriving (Eq, Ord)

newtype IndexVar = IndexVar Int deriving (Eq, Ord)

data Coefficient 
  = COEVar CoeffVar 
  | COENumeral Double 
  | COEAdd Coefficient Coefficient 
  | COEMul Coefficient Coefficient 
  deriving (Ord, Eq)

type Index = (Map IndexVar Coefficient, Coefficient)

data IndexVarConstraint = IVCLessEq Index Index deriving (Ord, Eq)

type IndexVarConstraintEnv = (Set IndexVar, Set IndexVarConstraint)


instance Show CoeffVar where

  show (CoeffVar n) = 'a' : show n


instance Show IndexVar where

  show (IndexVar n) = 'i' : show n
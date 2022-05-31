module Index
  ( CoeffVar (..),
    IndexVar (..),
    Coefficient (..),
    Index (..),
    IndexVarConstraint (..),
    IndexVarConstraintEnv,
    (.+),
    (.*),
    indexSubst,
    applyISubst
  )
where

import Data.Map as Map
import Data.Set as Set

newtype CoeffVar = CoeffVar Int deriving (Eq, Ord)

newtype IndexVar = IndexVar Int deriving (Eq, Ord)

data Coefficient 
  = COEVar CoeffVar 
  | COENumeral Integer
  | COEAdd Coefficient Coefficient 
  | COEMul Coefficient Coefficient 
  deriving (Ord, Eq)

newtype Index = Index (Map IndexVar Coefficient, Coefficient) deriving (Ord, Eq)

data IndexVarConstraint = IVCLessEq Index Index deriving (Ord, Eq)

type IndexVarConstraintEnv = (Set IndexVar, Set IndexVarConstraint)


instance Show IndexVarConstraint where

  show (IVCLessEq ix jx) = show ix ++ " <= " ++ show jx


instance Show CoeffVar where

  show (CoeffVar n) = 'a' : show n


instance Show IndexVar where

  show (IndexVar n) = 'i' : show n


instance Show Coefficient where

  show (COEVar alpha) = show alpha
  show (COENumeral n) = show n
  show (COEAdd c c') = "(" ++ show c ++ "+" ++ show c' ++ ")"
  show (COEMul c c') = show c ++ show c'


instance Show Index where

  show (Index (m, c)) = show c ++ Map.foldrWithKey (\i c' s -> show c ++ show i ++ " + " ++ s) "" m 


(.+) :: Index -> Index -> Index
(.+) (Index (m, c)) (Index (m', c')) = Index (Map.unionWith COEAdd m m', COEAdd c c')

(.*) :: Coefficient -> Index -> Index
(.*) c (Index (m', c')) = Index (Map.map (COEMul c) m', COEMul c c')

indexSubst :: Index -> Map IndexVar Index -> Index
indexSubst (Index (m, c)) subst = Map.foldr (.+) (Index (Map.empty, c)) $ Map.mapWithKey factor subst
  where
    factor i ix =
      case Map.lookup i m of
        Just c' -> c' .* ix
        _ -> ix

  
applyISubst :: Map CoeffVar Integer -> Index -> Index
applyISubst substI (Index (m, c)) = Index (Map.map aux m, aux c)
  where
    aux c'@(COEVar alpha) =
      case Map.lookup alpha substI of
        Just num -> COENumeral num
        _ -> c'

    aux c'@(COENumeral _) = c'
    aux (COEAdd c' c'') = COEAdd (aux c') (aux c'')
    aux (COEMul c' c'') = COEMul (aux c') (aux c'')

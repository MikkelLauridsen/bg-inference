module Index
  ( CoeffVar (..),
    IndexVar (..),
    Coefficient (..),
    Index (..),
    IndexVarConstraint (..),
    IndexVarConstraintEnv,
    (.+),
    (.*),
    (./),
    (.-),
    (.!),
    indexSubst,
    applyISubst
  )
where

import Data.Map as Map
import Data.Set as Set
import Data.List (intercalate)

newtype CoeffVar = CoeffVar Int deriving (Eq, Ord)

newtype IndexVar = IndexVar Int deriving (Eq, Ord)

data Coefficient 
  = COEVar CoeffVar 
  | COENumeral Integer
  | COEAdd Coefficient Coefficient 
  | COEMul Coefficient Coefficient 
  | COESub Coefficient Coefficient
  | COEDiv Coefficient Coefficient
  deriving (Ord, Eq)

newtype Index = Index (Map IndexVar Coefficient, Coefficient) deriving (Ord, Eq)

data IndexVarConstraint = IVCLessEq Index Index deriving (Ord, Eq)

type IndexVarConstraintEnv = (Set IndexVar, Set IndexVarConstraint)


instance Show IndexVarConstraint where

  show (IVCLessEq ix jx) = show ix ++ " \\leq " ++ show jx


instance Show CoeffVar where

  show (CoeffVar n) = "\\alpha_{" ++ show n ++ "}"


instance Show IndexVar where

  show (IndexVar n) = "i_{" ++ show n ++ "}"


instance Show Coefficient where

  show (COEVar alpha) = show alpha
  show (COENumeral n) = show n
  show (COEAdd c c') = "\\left(" ++ show c ++ "+" ++ show c' ++ "\\right)"
  show (COEMul c c') = show c ++ "\\left(" ++ show c' ++ "\\right)"
  show (COESub c c') = "\\left(" ++ show c ++ "-" ++ show c' ++ "\\right)"
  show (COEDiv c c') = "\\left(" ++ show c ++ "\\right)/\\left(" ++ show c' ++ "\\right)" 


instance Show Index where

  show (Index (m, c)) = intercalate " + " (show c : Prelude.map (\(i, c') -> show c' ++ show i) (Map.assocs m))


(.+) :: Index -> Index -> Index
(.+) (Index (m, c)) (Index (m', c')) = Index (Map.unionWith COEAdd m m', COEAdd c c')

(.*) :: Coefficient -> Index -> Index
(.*) c (Index (m', c')) = Index (Map.map (COEMul c) m', COEMul c c')

(./) :: Index -> Coefficient -> Index
(./) (Index (m, c)) c' = Index (Map.map ((flip COEDiv) c') m, COEDiv c c')

(.-) :: Index -> Index -> Index
(.-) (Index (m, c)) (Index (m', c')) = Index (Map.unionWith COEAdd m (Map.map (COESub (COENumeral 0)) m'), COESub c c')

(.!) :: Index -> Index
(.!) (Index (m, c)) = Index (Map.map (COESub (COENumeral 0)) m, COESub (COENumeral 0) c)

indexSubst :: Index -> Map IndexVar Index -> Index
indexSubst (Index (m, c)) subst = Map.foldr (.+) (Index (Map.empty, c)) $ Map.mapWithKey factor m
  where
    factor i c' =
      case Map.lookup i subst of
        Just ix -> c' .* ix
        _ -> Index (Map.singleton i c', COENumeral 0)

  
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

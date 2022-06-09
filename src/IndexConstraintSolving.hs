module IndexConstraintSolving
  ( solveIndexConstraints,
  )
where

import Constraints
import Data.Functor ((<&>))
import Data.List (union)
import qualified Data.Map as Map
import Data.Maybe
import Index
import Z3.Monad

data CoefficientConstraint = CCSEqual Coefficient Coefficient | CCSLessEq Coefficient Coefficient | CCSFalse

instance Show CoefficientConstraint where
  show (CCSEqual a b) = show a ++ " == " ++ show b
  show (CCSLessEq a b) = show a ++ " <= " ++ show b
  show CCSFalse = "false"

zeroCoeff = COENumeral 0

reduceIndexConstraints :: [IndexConstraint] -> [CoefficientConstraint]
reduceIndexConstraints [] = []
reduceIndexConstraints (ICSEqual (Index (ix1m, ix1b)) (Index (ix2m, ix2b)) : r) =
  CCSEqual ix1b ix2b :
  Prelude.map (\k -> CCSEqual (Map.findWithDefault zeroCoeff k ix1m) (Map.findWithDefault zeroCoeff k ix2m)) (Map.keys ix1m `union` Map.keys ix2m)
    ++ reduceIndexConstraints r
reduceIndexConstraints (ICSLessEq env (Index (ix1m, ix1b)) (Index (ix2m, ix2b)) : r) =
  CCSLessEq ix1b ix2b :
  Prelude.map (\k -> CCSLessEq (Map.findWithDefault zeroCoeff k ix1m) (Map.findWithDefault zeroCoeff k ix2m)) (Map.keys ix1m `union` Map.keys ix2m)
    ++ reduceIndexConstraints r
reduceIndexConstraints (ICSFalse : r) = CCSFalse : reduceIndexConstraints r

solveIndexConstraints :: [IndexConstraint] -> IO (Either String (Map.Map CoeffVar Integer))
solveIndexConstraints constraints = do
  res <- evalZ3 script
  case res of
    Just (Sat, vars) -> return $ Right vars
    Just (Unsat, _) -> return $ Left "Unsatisfiable"
    Just (a, vars) -> return $ Left $ "Unknown error: Just (" ++ show a ++ ", " ++ show vars ++ ")"
    Nothing -> return $ Left "No solution"
  where
    coefficientConstraints = reduceIndexConstraints constraints
    script = do
      (asts, vMaps) <- mapM coefficientConstraintToZ3 coefficientConstraints <&> unzip
      let vMaps' = concat vMaps
      let (vars, varAsts) = unzip vMaps'
      mapM_ optimizeAssert asts
      getObjectiveFunction vars >>= optimizeMinimize
      res <- optimizeCheck []
      case res of
        Sat -> do
          m <- optimizeGetModel
          mVals <- mapM (evalInt m) varAsts <&> catMaybes
          return $ Just (Sat, Map.fromList (zip vars mVals))
        a -> return $ Just (a, Map.empty)

coefficientConstraintToZ3 :: CoefficientConstraint -> Z3 (AST, [(CoeffVar, AST)])
coefficientConstraintToZ3 (CCSEqual c1 c2) = do
  (z1, m1) <- coefficientToZ3 c1
  (z2, m2) <- coefficientToZ3 c2
  ast <- mkEq z1 z2
  return (ast, m1 ++ m2)
coefficientConstraintToZ3 (CCSLessEq c1 c2) = do
  (z1, m1) <- coefficientToZ3 c1
  (z2, m2) <- coefficientToZ3 c2
  ast <- mkLe z1 z2
  return (ast, m1 ++ m2)
coefficientConstraintToZ3 CCSFalse = do
  ast <- mkFalse
  return (ast, [])

getObjectiveFunction :: [CoeffVar] -> Z3 AST
getObjectiveFunction [] = mkIntNum 0
getObjectiveFunction (v : vs) = do
  obj <- getObjectiveFunction vs
  var <- coefficientVarToZ3 v
  mkAdd [obj, var]

coefficientToZ3 :: Coefficient -> Z3 (AST, [(CoeffVar, AST)])
coefficientToZ3 (COEVar v) = do
  var <- coefficientVarToZ3 v
  _0 <- mkIntNum 0
  --optimizeAssert =<< mkGe var _0
  return (var, [(v, var)])
coefficientToZ3 (COENumeral n) = do
  ast <- mkIntNum n
  return (ast, [])
coefficientToZ3 (COEAdd c1 c2) = do
  (z1, m1) <- coefficientToZ3 c1
  (z2, m2) <- coefficientToZ3 c2
  ast <- mkAdd [z1, z2]
  return (ast, m1 ++ m2)
coefficientToZ3 (COEMul c1 c2) = do
  (z1, m1) <- coefficientToZ3 c1
  (z2, m2) <- coefficientToZ3 c2
  ast <- mkMul [z1, z2]
  return (ast, m1 ++ m2)

coefficientVarToZ3 :: CoeffVar -> Z3 AST
coefficientVarToZ3 (CoeffVar v) = do
  sym <- mkIntSymbol v
  mkIntVar sym
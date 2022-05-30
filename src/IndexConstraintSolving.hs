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

zeroCoeff = COENumeral 0

reduceIndexConstraints :: [IndexConstraint] -> [CoefficientConstraint]
reduceIndexConstraints [] = []
reduceIndexConstraints (ICSIndexEqual (ix1m, ix1b) (ix2m, ix2b) : r) =
  CCSEqual ix1b ix2b :
  Prelude.map (\k -> CCSEqual (Map.findWithDefault zeroCoeff k ix1m) (Map.findWithDefault zeroCoeff k ix1m)) (Map.keys ix1m `union` Map.keys ix2m)
    ++ reduceIndexConstraints r
reduceIndexConstraints (ICSLessEq env (ix1m, ix1b) (ix2m, ix2b) : r) =
  CCSLessEq ix1b ix2b :
  Prelude.map (\k -> CCSLessEq (Map.findWithDefault zeroCoeff k ix1m) (Map.findWithDefault zeroCoeff k ix1m)) (Map.keys ix1m `union` Map.keys ix2m)
    ++ reduceIndexConstraints r
reduceIndexConstraints (ICSFalse : r) = CCSFalse : reduceIndexConstraints r


solveIndexConstraints :: [IndexConstraint] -> IO (Either String (Map.Map CoefficientVar Rational))
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
      mapM_ assert asts
      fmap snd $
        withModel $ \m -> do
          let (vars, varAsts) = unzip vMaps'
          mVals <- mapM (evalReal m) varAsts <&> catMaybes
          return (Sat, Map.fromList (zip vars mVals))

coefficientConstraintToZ3 :: CoefficientConstraint -> Z3 (AST, [(CoefficientVar, AST)])
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

coefficientToZ3 :: Coefficient -> Z3 (AST, [(CoefficientVar, AST)])
coefficientToZ3 (COEVar v) = do
  sym <- mkIntSymbol v
  ast <- mkRealVar sym
  return (ast, [(v, ast)])
coefficientToZ3 (COENumeral n) = do
  ast <- mkRealNum 2
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

module IndexConstraintSolving
  ( solveIndexConstraints,
    positiveCoeff,
    reduceIndexConstraints,
    CoefficientConstraint(..)
  )
where

import Constraints
import Control.Monad
import Data.Foldable (find)
import Data.Functor ((<&>))
import Data.List as List (union)
import Data.Map as Map
import Data.Maybe
import Data.Set as Set
import Debug.Trace (trace)
import Index
import Z3.Monad

data CoefficientConstraint = CCSEqual Coefficient Coefficient | CCSLessEq Coefficient Coefficient | CCSFalse

instance Show CoefficientConstraint where
  show (CCSEqual a b) = show a ++ " == " ++ show b
  show (CCSLessEq a b) = show a ++ " <= " ++ show b
  show CCSFalse = "false"

zeroCoeff = COENumeral 0

reduceIndexConstraints :: Set CoeffVar -> [IndexConstraint] -> [CoefficientConstraint]
reduceIndexConstraints _ [] = []
reduceIndexConstraints positiveCoeffVars (ICSEqual (Index (ix1m, ix1b)) (Index (ix2m, ix2b)) : r) =
  CCSEqual ix1b ix2b :
  Prelude.map (\k -> CCSEqual (Map.findWithDefault zeroCoeff k ix1m) (Map.findWithDefault zeroCoeff k ix2m)) (Map.keys ix1m `List.union` Map.keys ix2m)
    ++ reduceIndexConstraints positiveCoeffVars r
reduceIndexConstraints positiveCoeffVars (ICSLessEq env@(_, phi) ix jx : r) =
  CCSLessEq ix1b ix2b :
  Prelude.map (\k -> CCSLessEq (Map.findWithDefault zeroCoeff k ix1m) (Map.findWithDefault zeroCoeff k ix2m)) (Map.keys ix1m `List.union` Map.keys ix2m)
    ++ reduceIndexConstraints positiveCoeffVars r
  where
    Index (ix1m, ix1b) = indexSubst ix subst
    Index (ix2m, ix2b) = indexSubst jx subst

    subst = Set.foldr (compose . indexVarConstraintToSubst positiveCoeffVars) Map.empty phi
    compose subst' subst'' = Map.map (`indexSubst` subst') subst'' `Map.union` subst'
reduceIndexConstraints positiveCoeffVars (ICSFalse : r) = CCSFalse : reduceIndexConstraints positiveCoeffVars r

solveIndexConstraints :: Set CoeffVar -> [IndexConstraint] -> Maybe Index -> IO (Either String (Map.Map CoeffVar Integer))
solveIndexConstraints positiveCoeffVars constraints mObjIndex = do
  res <- evalZ3 script
  case res of
    Just (Sat, vars) -> return $ Right vars
    Just (Unsat, _) -> return $ Left "Unsatisfiable"
    Just (a, vars) -> return $ Left $ "Unknown error: Just (" ++ show a ++ ", " ++ show vars ++ ")"
    Nothing -> return $ Left "No solution"
  where
    coefficientConstraints = reduceIndexConstraints positiveCoeffVars constraints
    script = do
      (asts, vMaps) <- mapM coefficientConstraintToZ3 coefficientConstraints <&> unzip
      let vMaps' = concat vMaps
      let (vars, varAsts) = unzip vMaps'
      mapM_ optimizeAssert asts
      case mObjIndex of
        Just ix -> getIndexObjectiveFunction ix >>= optimizeMinimize
        Nothing -> return 0
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

getIndexObjectiveFunction :: Index -> Z3 AST
getIndexObjectiveFunction (Index (m, b)) = do
  _0 <- mkIntNum 0
  foldM ffunc _0 (b : Map.elems m)
  where
    ffunc :: AST -> Coefficient -> Z3 AST
    ffunc obj c = do
      (var, _) <- coefficientToZ3 c
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
coefficientToZ3 (COESub c1 c2) = do
  (z1, m1) <- coefficientToZ3 c1
  (z2, m2) <- coefficientToZ3 c2
  ast <- mkSub [z1, z2]
  return (ast, m1 ++ m2)
coefficientToZ3 (COEDiv c1 c2) = do
  (z1, m1) <- coefficientToZ3 c1
  (z2, m2) <- coefficientToZ3 c2
  ast <- mkDiv z1 z2
  return (ast, m1 ++ m2)

coefficientVarToZ3 :: CoeffVar -> Z3 AST
coefficientVarToZ3 (CoeffVar v) = do
  sym <- mkIntSymbol v
  mkIntVar sym

indexVarConstraintToSubst :: Set CoeffVar -> IndexVarConstraint -> Map IndexVar Index
indexVarConstraintToSubst positiveCoeffVars (IVCLessEq ix (Index (m', c'))) =
  case find (positiveCoeff positiveCoeffVars . snd) $ Map.assocs m' of
    Just (i, c) -> Map.singleton i $ (ix .- Index (Map.delete i m', c')) ./ c
    _ -> Map.empty

positiveCoeff :: Set CoeffVar -> Coefficient -> Bool
positiveCoeff positiveCoeffVars (COEVar alpha) | Set.member alpha positiveCoeffVars = True
positiveCoeff _ (COENumeral n) | n > 0 = True
positiveCoeff positiveCoeffVars (COEAdd c c') = (positiveCoeff positiveCoeffVars c && nonnegativeCoeff positiveCoeffVars c') || (nonnegativeCoeff positiveCoeffVars c && positiveCoeff positiveCoeffVars c')
positiveCoeff positiveCoeffVars (COEMul c c') = positiveCoeff positiveCoeffVars c && positiveCoeff positiveCoeffVars c'
positiveCoeff positiveCoeffVars (COESub c c') = positiveCoeff positiveCoeffVars c && nonpositiveCoeff positiveCoeffVars c'
positiveCoeff positiveCoeffVars (COEDiv c c') = positiveCoeff positiveCoeffVars c && positiveCoeff positiveCoeffVars c'
positiveCoeff _ _ = False

nonnegativeCoeff :: Set CoeffVar -> Coefficient -> Bool
nonnegativeCoeff positiveCoeffVars (COEVar alpha) | Set.member alpha positiveCoeffVars = True
nonnegativeCoeff _ (COENumeral n) | n >= 0 = True
nonnegativeCoeff positiveCoeffVars (COEAdd c c') = nonnegativeCoeff positiveCoeffVars c && nonnegativeCoeff positiveCoeffVars c'
nonnegativeCoeff positiveCoeffVars (COEMul c c') = nonnegativeCoeff positiveCoeffVars c && nonnegativeCoeff positiveCoeffVars c'
nonnegativeCoeff positiveCoeffVars (COESub c c') = nonnegativeCoeff positiveCoeffVars c && nonpositiveCoeff positiveCoeffVars c'
nonnegativeCoeff positiveCoeffVars (COEDiv c c') = nonnegativeCoeff positiveCoeffVars c && positiveCoeff positiveCoeffVars c'
nonnegativeCoeff _ _ = False

nonpositiveCoeff :: Set CoeffVar -> Coefficient -> Bool
nonpositiveCoeff _ (COENumeral n) | n < 0 = True
nonpositiveCoeff positiveCoeffVars (COEAdd c c') = nonpositiveCoeff positiveCoeffVars c && nonpositiveCoeff positiveCoeffVars c'
nonpositiveCoeff positiveCoeffVars (COEMul c c') = (nonpositiveCoeff positiveCoeffVars c && nonnegativeCoeff positiveCoeffVars c') || (nonnegativeCoeff positiveCoeffVars c && nonpositiveCoeff positiveCoeffVars c')
nonpositiveCoeff positiveCoeffVars (COESub c c') = nonpositiveCoeff positiveCoeffVars c && nonnegativeCoeff positiveCoeffVars c'
nonpositiveCoeff positiveCoeffVars (COEDiv c c') = nonpositiveCoeff positiveCoeffVars c && positiveCoeff positiveCoeffVars c'
nonpositiveCoeff _ _ = False
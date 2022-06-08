{-# LANGUAGE FlexibleInstances #-}

module Inference
  ( inferSimpleTypes,
  )
where

import qualified ConstraintSolving as CS
import qualified Constraints as C
import qualified Control.Arrow as Data.Bifunctor
import Control.Exception
import Control.Monad.Except
import Control.Monad.State.Lazy
import qualified Data.Map as Map
import Data.Set as Set (Set, fromList, empty)
import Control.Monad (mapM)
import Data.Maybe
import Debug.Trace
import Index
import PiCalculus
import Types

data InferState = InferState
  { tvarCount :: Int,
    ivarCount :: Int,
    stack :: [(String, [(String, String)])],
    simpleTypeConstraints :: [C.SimpleTypeConstraint],
    simpleTypeContext :: Map.Map Var SimpleType, -- Maps
    ivarsPerServer :: Int
  }

type Infer a = StateT InferState (Either (InferState, String)) a

instance MonadFail (Either (InferState, String)) where
  fail s = Left (defaultState 0, s)

defaultState :: Int -> InferState
defaultState = InferState 0 0 [] [] Map.empty

runInfer :: Int -> Infer a -> Either String a
runInfer ivarsPerServer m = case evalStateT m (defaultState ivarsPerServer) of
  Left (InferState _ _ s _ _ _, msg) ->
    Left $
      "Error during process check: " ++ msg ++ "\n"
        ++ "StackTrace: "
        ++ show (Prelude.map fst s)
        ++ "\n"
        ++ "Relevant bindings: "
        ++ (if not (Prelude.null s) then (showBindings . snd . head) s else "Invalid")
        ++ "Relevant bindings 2: "
        ++ (if Prelude.length s >= 2 then (showBindings . snd . head . tail) s else "Invalid")
        ++ "Relevant bindings 3: "
        ++ (if Prelude.length s >= 3 then (showBindings . snd . head . tail . tail) s else "Invalid")
  Right k -> Right k
  where
    showBindings bindings = "\n" ++ Prelude.foldr (\(var, t) acc -> "  " ++ var ++ " : " ++ t ++ "\n" ++ acc) "" bindings

inferSimpleTypes :: Int -> Proc -> Either String SimpleTypeSubstitution
inferSimpleTypes ivarsPerServer p =
  runInfer ivarsPerServer $ do
    updateTvarCount p
    inferSimpleConstraintTypes p
    simpleTypeContext <- gets simpleTypeContext
    solveSimpleTypeConstraints >>= inferIndexVariables

solveSimpleTypeConstraints :: Infer SimpleTypeSubstitution
solveSimpleTypeConstraints = do
  s <- get
  let simpleConstraints = simpleTypeConstraints s
  case CS.solveSimpleTypeConstraints simpleConstraints of
    Left s -> fail $ "Could not solve simple type constraints: " ++ s
    Right subst -> return subst

returnError :: String -> Infer a
returnError msg = do
  s <- get
  throwError (s, msg)

inferIndexVariables :: SimpleTypeSubstitution -> Infer SimpleTypeSubstitution
inferIndexVariables = mapM $ \st ->
    case st of
      (STServ _ sts) -> freshServerIvars (Prelude.foldr ((+) . countIvars) 0 sts) >>= (\ixs -> return $ STServ ixs sts)
      _ -> return st
  where
    countIvars STNat = 2
    countIvars _ = 0

inContext :: String -> [(String, String)] -> Infer a -> Infer a
inContext name bindings action = do
  modify $ \st -> st {stack = (name, Prelude.map (Data.Bifunctor.second show) bindings) : stack st}
  res <- action
  modify $ \st -> st {stack = tail $ stack st}
  return res

freshTvar :: Infer TypeVar
freshTvar = do
  count <- gets tvarCount
  modify $ \s -> s {tvarCount = count + 1}
  return count

freshIvar :: Infer IndexVar
freshIvar = do
  count <- gets ivarCount
  modify $ \s -> s {ivarCount = count + 1}
  return $ IndexVar count

freshServerIvars :: Int -> Infer (Set IndexVar)
freshServerIvars num = do
  count <- gets ivarCount
  modify $ \s -> s {ivarCount = count + 1}
  return $ Set.fromList (Prelude.map IndexVar [count .. count + num - 1])

lookupSimpleType :: Var -> Infer SimpleType
lookupSimpleType v = do
  ctx <- gets simpleTypeContext
  case Map.lookup v ctx of
    Just t -> return t
    Nothing -> returnError $ "Error: variable " ++ show v ++ " not found in simple type context"

updateSimpleType :: Var -> SimpleType -> Infer ()
updateSimpleType v t = modify $ \s -> s {simpleTypeContext = Map.insert v t (simpleTypeContext s)}

maxTvarTyp :: SimpleType -> TypeVar
maxTvarTyp (STVar v) = v
maxTvarTyp STNat = -1
maxTvarTyp (STChannel ts) = maximum $ map maxTvarTyp ts
maxTvarTyp (STServ _ ts) = maximum $ map maxTvarTyp ts

maxTvar :: Proc -> TypeVar
maxTvar NilP = -1
maxTvar (TickP p) = maxTvar p
maxTvar (p1 :|: p2) = max (maxTvar p1) (maxTvar p2)
maxTvar (InputP _ _ p) = maxTvar p
maxTvar (OutputP _ _) = -1
maxTvar (RepInputP _ _ p) = maxTvar p
maxTvar (RestrictP _ t p) = max (maxTvar p) (maxTvarTyp t)
maxTvar (MatchNatP _ p1 _ p2) = max (maxTvar p1) (maxTvar p2)

updateTvarCount :: Proc -> Infer ()
updateTvarCount p =
  let count = maxTvar p + 1
   in modify $ \s -> s {tvarCount = count}

assertSimpleTypeConstraint :: C.SimpleTypeConstraint -> Infer ()
assertSimpleTypeConstraint c = do
  s <- get
  put $ s {simpleTypeConstraints = c : simpleTypeConstraints s}

-- TODO it is assumed all variable names are unique

inferExpSimpleType :: Exp -> Infer SimpleType
inferExpSimpleType ZeroE = inContext "ZeroE" [] $ return STNat
inferExpSimpleType (SuccE e) = inContext "SuccE" [] $ do
  t <- inferExpSimpleType e
  case t of
    STNat -> return STNat
    beta@(STVar _) -> assertSimpleTypeConstraint (C.STCSEqual beta STNat) >> return beta
    _ -> returnError "error: succ of non-nat"
inferExpSimpleType (VarE v) = inContext "VarE" [] $ lookupSimpleType v

inferSimpleConstraintTypes :: Proc -> Infer ()
inferSimpleConstraintTypes NilP = return ()
inferSimpleConstraintTypes (TickP p) = inContext "TickP" [] $ inferSimpleConstraintTypes p
inferSimpleConstraintTypes (p1 :|: p2) = inContext "ParP" [("p1", show p1), ("p2", show p2)] $ do
  inferSimpleConstraintTypes p1
  inferSimpleConstraintTypes p2
inferSimpleConstraintTypes (InputP v vs p) = inContext "InputP" [] $ do
  t <- lookupSimpleType v
  ts <- forM vs $ \v -> do
    t <- freshTvar
    updateSimpleType v (STVar t)
    return t
  assertSimpleTypeConstraint $ C.STCSEqual t (STChannel (map STVar ts))
  inferSimpleConstraintTypes p
inferSimpleConstraintTypes (OutputP v es) = inContext "OutputP" [] $ do
  t <- lookupSimpleType v
  ts <- mapM inferExpSimpleType es
  assertSimpleTypeConstraint $ C.STCSChannelServer t ts
inferSimpleConstraintTypes (RepInputP a vs p) = inContext "RepInputP" [] $ do
  t <- lookupSimpleType a
  ts <- forM vs $ \v -> do
    t <- freshTvar
    updateSimpleType v (STVar t)
    return t
  -- ixs <- freshServerIvars
  assertSimpleTypeConstraint $ C.STCSEqual t (STServ Set.empty (map STVar ts))
  inferSimpleConstraintTypes p
inferSimpleConstraintTypes (RestrictP v t p) = inContext "RestrictP" [] $ do
  updateSimpleType v t
  inferSimpleConstraintTypes p
inferSimpleConstraintTypes (MatchNatP e p1 v p2) = inContext "MatchNatP" [] $ do
  t <- inferExpSimpleType e
  assertSimpleTypeConstraint $ C.STCSEqual t STNat
  ntv <- freshTvar
  assertSimpleTypeConstraint $ C.STCSEqual (STVar ntv) STNat
  inferSimpleConstraintTypes p1
  updateSimpleType v (STVar ntv)
  inferSimpleConstraintTypes p2




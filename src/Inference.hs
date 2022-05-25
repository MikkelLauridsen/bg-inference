{-# LANGUAGE FlexibleInstances #-}

module Inference () where

import qualified Constraints as C
import Control.Exception
import Control.Monad.Except
import Control.Monad.State.Lazy
import qualified Data.Map as Map
import PiCalculus
import Types

data InferState = InferState
  { tvarCount :: Int,
    ivarCount :: Int,
    stack :: [(String, [(String, String)])],
    constraints :: [C.Constraint],
    simpleTypeContext :: Map.Map Var SimpleType,
    ivarsPerServer :: Int
  }

type Infer a = StateT InferState (Either (InferState, String)) a

instance MonadFail (Either (InferState, String)) where
  fail s = Left (InferState 0 0 [] [] Map.empty 0, s)

returnError :: String -> Infer a
returnError msg = do
  s <- get
  throwError (s, msg)

freshTvar :: Infer TypeVar
freshTvar = do
  count <- gets tvarCount
  modify $ \s -> s {tvarCount = count + 1}
  return count

freshIvar :: Infer IndexVar
freshIvar = do
  count <- gets ivarCount
  modify $ \s -> s {ivarCount = count + 1}
  return count

freshServerIvars :: Infer [IndexVar]
freshServerIvars = do
  count <- gets ivarsPerServer
  modify $ \s -> s {ivarCount = count + 1}
  return [count .. count + count - 1]

lookupSimpleType :: Var -> Infer SimpleType
lookupSimpleType v = do
  ctx <- gets simpleTypeContext
  case Map.lookup v ctx of
    Just t -> return t
    Nothing -> returnError "error: variable not in context"

updateSimpleType :: Var -> SimpleType -> Infer ()
updateSimpleType v t = modify $ \s -> s {simpleTypeContext = Map.insert v t (simpleTypeContext s)}

maxTvarTyp :: SimpleType -> TypeVar
maxTvarTyp (STVar v) = v
maxTvarTyp STNat = 0
maxTvarTyp (STChannel ts) = maximum $ map maxTvarTyp ts
maxTvarTyp (STServ _ ts) = maximum $ map maxTvarTyp ts

maxTvar :: Proc -> TypeVar
maxTvar NilP = 0
maxTvar (TickP p) = maxTvar p
maxTvar (p1 :|: p2) = max (maxTvar p1) (maxTvar p2)
maxTvar (InputP _ _ p) = maxTvar p
maxTvar (OutputP _ _) = 0
maxTvar (RepInputP _ _ p) = maxTvar p
maxTvar (RestrictP _ t p) = max (maxTvar p) (maxTvarTyp t)
maxTvar (MatchNatP _ p1 _ p2) = max (maxTvar p1) (maxTvar p2)

updateTvarCount :: Proc -> Infer ()
updateTvarCount p =
  let count = maxTvar p
   in modify $ \s -> s {tvarCount = count}

assertConstraint :: C.Constraint -> Infer ()
assertConstraint c = do
  s <- get
  put $ s {constraints = c : constraints s}

-- TODO ensure all variables are unique

inferExpSimpleType :: Exp -> Infer SimpleType
inferExpSimpleType ZeroE = return STNat
inferExpSimpleType (SuccE e) = do
  t <- inferExpSimpleType e
  case t of
    STNat -> return STNat
    _ -> returnError "error: succ of non-nat"
inferExpSimpleType (VarE v) = lookupSimpleType v


inferSimpleConstraintTypes :: Proc -> Infer ()
inferSimpleConstraintTypes NilP = return ()
inferSimpleConstraintTypes (TickP p) = inferSimpleConstraintTypes p
inferSimpleConstraintTypes (p1 :|: p2) = do
  inferSimpleConstraintTypes p1
  inferSimpleConstraintTypes p2
inferSimpleConstraintTypes (InputP v vs p) = do
  t <- lookupSimpleType v
  ts <- forM vs $ \v -> do
    t <- freshTvar
    updateSimpleType v (STVar t)
    return t
  assertConstraint $ C.CSSimple $ C.STCSEqual t (STChannel (map STVar ts))
  inferSimpleConstraintTypes p
inferSimpleConstraintTypes (OutputP v es) = do
  t <- lookupSimpleType v
  ts <- mapM inferExpSimpleType es
  assertConstraint $ C.CSSimple $ C.STCSChannelServer t ts
inferSimpleConstraintTypes (RepInputP v vs p) = do
  t <- lookupSimpleType v
  ts <- forM vs $ \v -> do
    t <- freshTvar
    updateSimpleType v (STVar t)
    return t
  ixs <- freshServerIvars
  assertConstraint $ C.CSSimple $ C.STCSEqual t (STServ ixs (map STVar ts))
  inferSimpleConstraintTypes p
inferSimpleConstraintTypes (RestrictP v t p) = updateSimpleType v t >> inferSimpleConstraintTypes p
inferSimpleConstraintTypes (MatchNatP e p1 v p2) = do
  t <- inferExpSimpleType e
  assertConstraint $ C.CSSimple $ C.STCSEqual t STNat
  ntv <- freshTvar
  assertConstraint $ C.CSSimple $ C.STCSEqual (STVar ntv) STNat
  inferSimpleConstraintTypes p1
  inferSimpleConstraintTypes p2


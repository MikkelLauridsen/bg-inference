module ConstraintSolving
  ( solveSimpleTypeConstraints,
  )
where

import Constraints
import Control.Monad
import qualified Control.Monad
import Data.Function
import Data.Map as Map
import qualified Data.Maybe
import Data.Set as Set
import Debug.Trace
import Types
import PiCalculus

-- Simple types enriched with a type that may be eihter a channel or a server
data SimpleTypeEnriched
  = STEVar TypeVar
  | STENat
  | STEChannel [SimpleTypeEnriched]
  | STEServ (Set IndexVar) [SimpleTypeEnriched]
  | STEChannelOrServ [SimpleTypeEnriched]
  deriving (Show, Eq, Ord)

data SimpleTypeEnrichedConstraint = STECSEqual SimpleTypeEnriched SimpleTypeEnriched deriving (Eq, Ord)

instance Show SimpleTypeEnrichedConstraint where
  show (STECSEqual a b) = show a ++ " == " ++ show b

solveSimpleTypeConstraints :: [SimpleTypeConstraint] -> Either String SimpleTypeSubstitution
solveSimpleTypeConstraints constraints = do
  let constraints' = Set.fromList $ Prelude.map liftSTConstraint constraints
  let constraints'' = inferNewConstraints2 constraints' `Set.union` constraints'
  let constraints''' = inferNewConstraints constraints'' `Set.union` constraints''
  let constraints'''' = inferNewConstraints2 constraints''' `Set.union` constraints'''
  subPairs <- getSubstitutions (Set.toList constraints'''')
  subs <- fromListFailable combineSimpleTypes subPairs
  let subs' = refineSubstitutions subs
  return $ Map.map unliftSTEType subs'

liftSTType :: SimpleType -> SimpleTypeEnriched
liftSTType (STVar v) = STEVar v
liftSTType STNat = STENat
liftSTType (STChannel ts) = STEChannel (Prelude.map liftSTType ts)
liftSTType (STServ ts is) = STEServ ts (Prelude.map liftSTType is)

unliftSTEType :: SimpleTypeEnriched -> SimpleType
unliftSTEType (STEVar v) = STVar v
unliftSTEType STENat = STNat
unliftSTEType (STEChannel ts) = STChannel (Prelude.map unliftSTEType ts)
unliftSTEType (STEServ ts is) = STServ ts (Prelude.map unliftSTEType is)
unliftSTEType (STEChannelOrServ ts) = STChannel (Prelude.map unliftSTEType ts)

liftSTConstraint :: SimpleTypeConstraint -> SimpleTypeEnrichedConstraint
liftSTConstraint (STCSEqual t1 t2) = STECSEqual (liftSTType t1) (liftSTType t2)
liftSTConstraint (STCSChannelServer t ts) = STECSEqual (liftSTType t) (STEChannelOrServ (Prelude.map liftSTType ts))

fromListFailable :: (Monad m, Ord k) => (a -> a -> m a) -> [(k, a)] -> m (Map k a)
fromListFailable _ [] = return Map.empty
fromListFailable f ((k, v) : rest) = do
  rest' <- fromListFailable f rest
  case Map.lookup k rest' of
    Nothing -> return $ Map.insert k v rest'
    Just v' -> f v v' >>= \v'' -> return $ Map.insert k v'' rest'

inferNewConstraints :: Set SimpleTypeEnrichedConstraint -> Set SimpleTypeEnrichedConstraint
inferNewConstraints constraints = inferNewConstraints' (Set.toList constraints) constraints `Set.union` constraints

inferNewConstraints' :: [SimpleTypeEnrichedConstraint] -> Set SimpleTypeEnrichedConstraint -> Set SimpleTypeEnrichedConstraint
inferNewConstraints' [] _ = Set.empty
inferNewConstraints' (c : cs) constraints = inferNewConstraints'' c (Set.delete c constraints) `Set.union` inferNewConstraints' cs (Set.delete c constraints)

inferNewConstraints'' :: SimpleTypeEnrichedConstraint -> Set SimpleTypeEnrichedConstraint -> Set SimpleTypeEnrichedConstraint
inferNewConstraints'' constraint constraints = Set.unions $ Set.map (inferNewConstraints''' constraint) constraints

inferNewConstraints''' :: SimpleTypeEnrichedConstraint -> SimpleTypeEnrichedConstraint -> Set SimpleTypeEnrichedConstraint
inferNewConstraints''' (STECSEqual t1 t2) (STECSEqual t1' t2') | t1 == t1' = inferNewConstraints'''' t2 t2'
inferNewConstraints''' _ _ = Set.empty

inferNewConstraints'''' :: SimpleTypeEnriched -> SimpleTypeEnriched -> Set SimpleTypeEnrichedConstraint
inferNewConstraints'''' (STEVar a) t = Set.singleton $ STECSEqual (STEVar a) t
inferNewConstraints'''' t (STEVar a) = Set.singleton $ STECSEqual (STEVar a) t
inferNewConstraints'''' STENat STENat = Set.empty
inferNewConstraints'''' (STEChannel t1s) (STEChannel t2s) | length t1s == length t2s = Set.fromList $ zipWith STECSEqual t1s t2s
inferNewConstraints'''' (STEServ is t1s) (STEServ is' t2s) | length t1s == length t2s = Set.fromList $ zipWith STECSEqual t1s t2s
inferNewConstraints'''' (STEChannelOrServ t1s) (STEChannelOrServ t2s) | length t1s == length t2s = Set.fromList $ zipWith STECSEqual t1s t2s
inferNewConstraints'''' ((STEChannel t1s)) (STEChannelOrServ t2s) | length t1s == length t2s = Set.fromList $ zipWith STECSEqual t1s t2s
inferNewConstraints'''' (STEChannelOrServ t1s) ((STEChannel t2s)) | length t1s == length t2s = Set.fromList $ zipWith STECSEqual t1s t2s
inferNewConstraints'''' ((STEServ is t1s)) (STEChannelOrServ t2s) | length t1s == length t2s = Set.fromList $ zipWith STECSEqual t1s t2s
inferNewConstraints'''' (STEChannelOrServ t1s) ((STEServ is t2s)) | length t1s == length t2s = Set.fromList $ zipWith STECSEqual t1s t2s
inferNewConstraints'''' t1 t2 = Set.empty

inferNewConstraints2 :: Set SimpleTypeEnrichedConstraint -> Set SimpleTypeEnrichedConstraint
inferNewConstraints2 = Set.map (\(STECSEqual t1 t2) -> STECSEqual t2 t1)

getSubstitutions :: [SimpleTypeEnrichedConstraint] -> Either String [(TypeVar, SimpleTypeEnriched)]
getSubstitutions [] = return []
getSubstitutions (STECSEqual (STEVar v) t2 : r) = do
  s <- getSubstitutions r
  return ((v, t2) : s)
getSubstitutions (STECSEqual t1 (STEVar v) : r) = do
  s <- getSubstitutions r
  return ((v, t1) : s)
getSubstitutions (STECSEqual STENat STENat : r) = getSubstitutions r
getSubstitutions (STECSEqual (STEChannel t1s) (STEChannel t2s) : r) = getSubstitutions (r ++ zipWith STECSEqual t1s t2s)
getSubstitutions (STECSEqual (STEServ i1s t1s) (STEServ i2s t2s) : r) =
  if i1s == i2s
    then getSubstitutions (r ++ zipWith STECSEqual t1s t2s)
    else Left "Non-matching index variables"
getSubstitutions (a : r) = Left "Cannot get substitution"

refineSubstitutions :: Map TypeVar SimpleTypeEnriched -> Map TypeVar SimpleTypeEnriched
refineSubstitutions s = Map.map (refineSimpleTypeEnr s) s

refineSimpleTypeEnr :: Map TypeVar SimpleTypeEnriched -> SimpleTypeEnriched -> SimpleTypeEnriched
refineSimpleTypeEnr subs ((STEVar v)) =
  case Map.lookup v subs of
    Just t -> refineSimpleTypeEnr subs t
    Nothing -> STEVar v
refineSimpleTypeEnr subs STENat = STENat
refineSimpleTypeEnr subs ((STEChannel ts)) = STEChannel (Prelude.map (refineSimpleTypeEnr subs) ts)
refineSimpleTypeEnr subs ((STEServ i ts)) = STEServ i (Prelude.map (refineSimpleTypeEnr subs) ts)
refineSimpleTypeEnr subs (STEChannelOrServ ts) = STEChannelOrServ (Prelude.map (refineSimpleTypeEnr subs) ts)

combineSimpleTypes :: SimpleTypeEnriched -> SimpleTypeEnriched -> Either String SimpleTypeEnriched
combineSimpleTypes (STEVar a) t = return t
combineSimpleTypes t (STEVar a) = return t
combineSimpleTypes STENat STENat = return STENat
combineSimpleTypes (STEChannel t1s) (STEChannel t2s) | length t1s == length t2s = do
  ts <- zipWithM combineSimpleTypes t1s t2s
  return $ STEChannel ts
combineSimpleTypes (STEServ is t1s) (STEServ is' t2s) | length t1s == length t2s = do
  ts <- zipWithM combineSimpleTypes t1s t2s
  return $ STEServ is ts
combineSimpleTypes (STEChannelOrServ t1s) (STEChannelOrServ t2s) | length t1s == length t2s = do
  ts <- zipWithM combineSimpleTypes t1s t2s
  return $ STEChannelOrServ ts
combineSimpleTypes ((STEChannel t1s)) (STEChannelOrServ t2s) | length t1s == length t2s = do
  ts <- forM (zip t1s t2s) $ uncurry combineSimpleTypes
  return $ STEChannel ts
combineSimpleTypes (STEChannelOrServ t1s) ((STEChannel t2s)) | length t1s == length t2s = do
  ts <- forM (zip t1s t2s) $ uncurry combineSimpleTypes
  return $ STEChannel ts
combineSimpleTypes ((STEServ is t1s)) (STEChannelOrServ t2s) | length t1s == length t2s = do
  ts <- forM (zip t1s t2s) $ uncurry combineSimpleTypes
  return $ STEServ is ts
combineSimpleTypes (STEChannelOrServ t1s) ((STEServ is t2s)) | length t1s == length t2s = do
  ts <- forM (zip t1s t2s) $ uncurry combineSimpleTypes
  return $ STEServ is ts
combineSimpleTypes t1 t2 = Left $ "failed to combine types: " ++ show t1 ++ " and " ++ show t2
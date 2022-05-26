module ConstraintSolving
  ( solveSimpleTypeConstraints,
  )
where

import Constraints
import Control.Monad
import qualified Control.Monad
import Data.Map as Map
import qualified Data.Maybe
import Debug.Trace
import Types

-- Simple types enriched with a type that may be eihter a channel or a server
data SimpleTypeEnriched = STEVar TypeVar | STENat | STEChannel [SimpleTypeEnriched] | STEServ [IndexVar] [SimpleTypeEnriched] | STEChannelOrServ [SimpleTypeEnriched] deriving (Show)

type SimpleTypeEnrichedConstraint = (SimpleTypeEnriched, SimpleTypeEnriched)

solveSimpleTypeConstraints :: [SimpleTypeConstraint] -> Either String SimpleTypeSubstitution
solveSimpleTypeConstraints constraints = do
  let constraints' = Prelude.map liftSTConstraint constraints
  subPairs <- getSubstitutions constraints'
  subs <- trace (show subPairs) fromListFailable combineSimpleTypes subPairs
  let subs' = trace (show subs) refineSubstitutions subs
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
liftSTConstraint (STCSEqual t1 t2) = (liftSTType t1, liftSTType t2)
liftSTConstraint (STCSChannelServer t ts) = (liftSTType t, STEChannelOrServ (Prelude.map liftSTType ts))

fromListFailable :: Ord k => (a -> a -> Either String a) -> [(k, a)] -> Either String (Map.Map k a)
fromListFailable _ [] = return Map.empty
fromListFailable f ((k, v) : rest) = do
  rest' <- fromListFailable f rest
  case Map.lookup k rest' of
    Nothing -> return $ Map.insert k v rest'
    Just v' -> f v v' >>= \v'' -> return $ Map.insert k v'' rest'

getSubstitutions :: [SimpleTypeEnrichedConstraint] -> Either String [(TypeVar, SimpleTypeEnriched)]
getSubstitutions [] = return []
getSubstitutions ((STEVar v, t2) : r) = do
  s <- getSubstitutions r
  return ((v, t2) : s)
getSubstitutions ((t1, STEVar v) : r) = do
  s <- getSubstitutions r
  return ((v, t1) : s)
getSubstitutions ((STENat, STENat) : r) = getSubstitutions r
getSubstitutions ((STEChannel t1s, STEChannel t2s) : r) = getSubstitutions (r ++ zip t1s t2s)
getSubstitutions ((STEServ i1s t1s, STEServ i2s t2s) : r) =
  if i1s == i2s
    then getSubstitutions (r ++ zip t1s t2s)
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
combineSimpleTypes (STEChannel t1s) (STEChannel t2s) = do
  ts <- zipWithM combineSimpleTypes t1s t2s
  return $ STEChannel ts
combineSimpleTypes (STEServ is t1s) (STEServ is' t2s) = do
  ts <- zipWithM combineSimpleTypes t1s t2s
  return $ STEServ is ts
combineSimpleTypes (STEChannelOrServ t1s) (STEChannelOrServ t2s) = do
  ts <- zipWithM combineSimpleTypes t1s t2s
  return $ STEChannelOrServ ts
combineSimpleTypes ((STEChannel t1s)) (STEChannelOrServ t2s) = do
  ts <- forM (zip t1s t2s) $ uncurry combineSimpleTypes
  return $ STEChannel ts
combineSimpleTypes (STEChannelOrServ t1s) ((STEChannel t2s)) = do
  ts <- forM (zip t1s t2s) $ uncurry combineSimpleTypes
  return $ STEChannel ts
combineSimpleTypes ((STEServ is t1s)) (STEChannelOrServ t2s) = do
  ts <- forM (zip t1s t2s) $ uncurry combineSimpleTypes
  return $ STEServ is ts
combineSimpleTypes (STEChannelOrServ t1s) ((STEServ is t2s)) = do
  ts <- forM (zip t1s t2s) $ uncurry combineSimpleTypes
  return $ STEServ is ts
combineSimpleTypes _ _ = Left "failed to combine types"
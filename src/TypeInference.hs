{-# LANGUAGE FlexibleInstances #-}

module TypeInference
( inferTypes

) where

import Constraints
import Control.Exception
import Control.Monad.Except
import Control.Monad.State
import Control.Monad (when)
import Data.Set as Set
import Data.Map as Map
import Index
import PiCalculus
import Types

data InferState = InferState
  { nextCapabVar :: Int,
    nextCoeffVar :: Int,
    typeConstraints :: Set TypeConstraint
  }

type Infer a = StateT InferState (Either (InferState, String)) a

instance MonadFail (Either (InferState, String)) where
  fail serr = Left (initState, serr)

type SimpleEnv = Map Var SimpleType

type TypeEnv = Map Var Type


initState = InferState { nextCapabVar = 0, nextCoeffVar = 0, typeConstraints = Set.empty }


(.:) :: (Ord k) => Map k v -> (k, v) -> Map k v
(.:) m (key, val) = Map.insert key val m


inOut = UCSet $ Set.fromList [UCIn, UCOut]


freshCapabVar :: Infer CapabVar
freshCapabVar = do
    s <- get
    put s{ nextCapabVar = nextCapabVar s + 1 }
    return $ CapabVar (nextCapabVar s)


freshCoeffVar :: Infer CoeffVar
freshCoeffVar = do
    s <- get
    put s{ nextCoeffVar = nextCoeffVar s + 1 }
    return $ CoeffVar (nextCoeffVar s)


freshTemplate :: Set IndexVar -> Infer Index
freshTemplate vphi = do 
    alpha <- freshCoeffVar
    terms <- sequence [freshCoeffVar >>= (\alpha' -> return (i, COEVar alpha')) | i <- Set.toList vphi]
    return (Map.fromList terms, COEVar alpha)


freshType :: Set IndexVar -> SimpleType -> Infer Type
freshType vphi (STVar _) = fail "invalid simple types"
freshType vphi (STNat) = do
    ix <- freshTemplate vphi
    jx <- freshTemplate vphi
    return $ TNat ix jx

freshType vphi (STChannel sts) = do
    gamma <- freshCapabVar
    ix <- freshTemplate vphi
    ts <- sequence $ Prelude.map (freshType vphi) sts
    return $ TChannel (UCVar gamma) ix ts

freshType vphi (STServ is sts) = do
    gamma <- freshCapabVar
    ix <- freshTemplate vphi
    kx <- freshTemplate $ vphi `Set.union` is
    ts <- sequence $ Prelude.map (freshType $ vphi `Set.union` is) sts
    return $ TServ ix is (UCVar gamma) kx ts


(.~) :: TypeEnv -> TypeEnv -> Set TypeConstraint
(.~) tenv tenv' = Set.fromList [TCSEqual (tenv ! v) (tenv' ! v) | v <- Set.toList (Map.keysSet tenv `Set.intersection` Map.keysSet tenv')]


addConstraints :: Set TypeConstraint -> Infer ()
addConstraints cs = do
    s <- get
    put s{ typeConstraints = typeConstraints s `Set.union` cs }


addConstraint :: TypeConstraint -> Infer ()
addConstraint = addConstraints . Set.singleton


zeroIndex :: Set IndexVar -> Index
zeroIndex vphi = (Map.fromList $ Prelude.zip (Set.toList vphi) (Prelude.map COENumeral [0, 0 ..]), COENumeral 0) 


oneIndex :: Set IndexVar -> Index
oneIndex vphi = (Map.fromList $ Prelude.zip (Set.toList vphi) (Prelude.map COENumeral [0, 0 ..]), COENumeral 1) 


delay :: Index -> Type -> Type
delay _ t@(TNat _ _) = t
delay jx (TChannel sigma ix ts) = TChannel sigma (ix .+ jx) ts
delay jx (TServ ix is sigma kx ts) = TServ (ix .+ jx) is sigma kx ts


delayEnv :: Index -> TypeEnv -> TypeEnv
delayEnv jx = Map.map (delay jx)


inferTypes :: IndexVarConstraintEnv -> SimpleEnv -> Proc -> Either String (TypeEnv, Set TypeConstraint, Index)
inferTypes env senv p =
    case runStateT (inferProc env senv p) initState of
        Left (_, serr) -> Left serr
        Right ((tenv, kx), s) -> Right (tenv, typeConstraints s, kx)


inferExp :: IndexVarConstraintEnv -> SimpleEnv -> Exp -> Infer (TypeEnv, Type)
inferExp (vphi, _) senv ZeroE = freshTemplate vphi >>= (\jx -> return (Map.empty, TNat (zeroIndex vphi) jx))

inferExp (vphi, _) senv (VarE v) = 
    case Map.lookup v senv of
        Just st -> freshType vphi st >>= (\t -> return (Map.singleton v t, t))
        _ -> fail $ "name '" ++ show v ++ "' is free"

inferExp env@(vphi, _) senv (SuccE e) = do
    (tenv, t) <- inferExp env senv e
    ix <- freshTemplate vphi
    jx <- freshTemplate vphi
    ix' <- freshTemplate vphi
    jx' <- freshTemplate vphi
    addConstraint $ TCSEqual t (TNat ix jx)
    addConstraint $ TCSConditionalSubsumption [] env (TNat (ix .+ oneIndex vphi) (jx .+ oneIndex vphi)) (TNat ix'  jx')
    return (tenv, TNat ix' jx')


inferProc :: IndexVarConstraintEnv -> SimpleEnv -> Proc -> Infer (TypeEnv, Index)
inferProc env senv (RestrictP a st p) = do
    (tenv, kx) <- inferProc env (senv .: (a, st)) p
    case Map.lookup a tenv of
        Just (TChannel sigma _ _) -> addConstraint $ TCSUse (USCConditional [] (UCCSSubset inOut sigma))
        Just (TServ _ _ sigma _ _) -> addConstraint $ TCSUse (USCConditional [] (UCCSSubset inOut sigma))
        _ -> return ()
    return (Map.delete a tenv, kx)

inferProc (vphi, _) senv NilP = freshTemplate vphi >>= (\kx -> return (Map.empty, kx))

inferProc env senv (p :|: q) = do
    (tenv, kx) <- inferProc env senv p
    (tenv', kx') <- inferProc env senv q
    addConstraint $ TCSEqualIndex kx kx'
    addConstraints $ tenv .~ tenv'
    return (tenv `Map.union` tenv', kx)

inferProc env@(vphi, _) senv (TickP p) = do
    (tenv, kx) <- inferProc env senv p
    kx' <- freshTemplate vphi
    addConstraint $ TCSUse (USCConditionalInequality [] env (kx .+ (oneIndex vphi)) kx')
    return (delayEnv (oneIndex vphi) tenv, kx')

inferProc env@(vphi, phi) senv (MatchNatP e p x q) = do
    (tenv, TNat ix jx) <- inferExp (vphi, phi) senv e
    (tenv', kx) <- inferProc (vphi, Set.insert (IVCLessEq ix (zeroIndex vphi)) phi) senv p
    (tenv'', kx') <- inferProc (vphi, Set.insert (IVCLessEq (oneIndex vphi) jx) phi) (senv .: (x, STNat)) q
    addConstraint $ TCSEqualIndex kx kx'
    addConstraints $ tenv .~ tenv'
    addConstraints $ tenv .~ tenv''
    addConstraints $ tenv' .~ tenv''
    case Map.lookup x (tenv' `Map.union` tenv') of
        Just (TNat (m, c) (m', c')) -> addConstraint $ TCSConditionalSubsumption [] env (TNat ix jx) (TNat (m, COEAdd c (COENumeral 1)) (m', COEAdd c' (COENumeral 1)))
        _ -> return ()
    return (Map.delete x $ tenv `Map.union` tenv' `Map.union` tenv'', kx)


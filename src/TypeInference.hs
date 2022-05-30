{-# LANGUAGE FlexibleInstances #-}

module TypeInference
( inferTypes

) where

import Constraints
import Control.Exception
import Control.Monad.Except
import Control.Monad.State
import Control.Monad (when, mapM)
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
    return $ Index (Map.fromList terms, COEVar alpha)


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


assertConstraints :: Set TypeConstraint -> Infer ()
assertConstraints cs = do
    s <- get
    put s{ typeConstraints = typeConstraints s `Set.union` cs }


assertConstraint :: TypeConstraint -> Infer ()
assertConstraint = assertConstraints . Set.singleton


zeroIndex :: Set IndexVar -> Index
zeroIndex vphi = Index (Map.fromList $ Prelude.zip (Set.toList vphi) (Prelude.map COENumeral [0, 0 ..]), COENumeral 0) 


oneIndex :: Set IndexVar -> Index
oneIndex vphi = Index (Map.fromList $ Prelude.zip (Set.toList vphi) (Prelude.map COENumeral [0, 0 ..]), COENumeral 1) 


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
    assertConstraint $ TCSEqual t (TNat ix jx)
    assertConstraint $ TCSConditionalSubsumption [] env (TNat (ix .+ oneIndex vphi) (jx .+ oneIndex vphi)) (TNat ix'  jx')
    return (tenv, TNat ix' jx')


inferProc :: IndexVarConstraintEnv -> SimpleEnv -> Proc -> Infer (TypeEnv, Index)
inferProc env senv (RestrictP a st p) = do
    (tenv, kx) <- inferProc env (senv .: (a, st)) p
    case Map.lookup a tenv of
        Just (TChannel sigma _ _) -> assertConstraint $ TCSUse (USCConditional [] (UCCSSubset inOut sigma))
        Just (TServ _ _ sigma _ _) -> assertConstraint $ TCSUse (USCConditional [] (UCCSSubset inOut sigma))
        _ -> return ()
    return (Map.delete a tenv, kx)

inferProc (vphi, _) senv NilP = freshTemplate vphi >>= (\kx -> return (Map.empty, kx))

inferProc env senv (p :|: q) = do
    (tenv, kx) <- inferProc env senv p
    (tenv', kx') <- inferProc env senv q
    assertConstraint $ (TCSUse (USCIndex (ICSEqual kx kx')))
    assertConstraints $ tenv .~ tenv'
    return (tenv `Map.union` tenv', kx)

inferProc env@(vphi, _) senv (TickP p) = do
    (tenv, kx) <- inferProc env senv p
    kx' <- freshTemplate vphi
    assertConstraint $ TCSUse (USCConditionalInequality [] env (kx .+ (oneIndex vphi)) kx')
    return (delayEnv (oneIndex vphi) tenv, kx')

inferProc env@(vphi, phi) senv (MatchNatP e p x q) = do
    (tenv, TNat ix jx) <- inferExp (vphi, phi) senv e
    (tenv', kx) <- inferProc (vphi, Set.insert (IVCLessEq ix (zeroIndex vphi)) phi) senv p
    (tenv'', kx') <- inferProc (vphi, Set.insert (IVCLessEq (oneIndex vphi) jx) phi) (senv .: (x, STNat)) q
    assertConstraint $ (TCSUse (USCIndex (ICSEqual kx kx')))
    assertConstraints $ tenv .~ tenv'
    assertConstraints $ tenv .~ tenv''
    assertConstraints $ tenv' .~ tenv''
    case Map.lookup x (tenv' `Map.union` tenv') of
        Just (TNat (Index (m, c)) (Index (m', c'))) -> assertConstraint $ TCSConditionalSubsumption [] env (TNat ix jx) (TNat (Index (m, COEAdd c (COENumeral 1))) (Index (m', COEAdd c' (COENumeral 1))))
        _ -> return ()
    return (Map.delete x $ tenv `Map.union` tenv' `Map.union` tenv'', kx)

inferProc env@(vphi, _) senv (InputP a vs p) =
    case Map.lookup a senv of
        Just st@(STChannel sts) -> do
            (tenv, kx) <- inferProc env (Map.fromList (Prelude.zip vs sts) `Map.union` senv) p
            TChannel gamma ix ts <- freshType vphi st
            kx' <- freshTemplate vphi
            let tenv' = Map.fromList $ (a, TChannel gamma ix ts) : Prelude.zip vs ts
            assertConstraints $ Set.fromList [TCSConditionalSubsumption [] env (tenv' ! w) (tenv ! w) | w <- Map.keys tenv', Map.member w tenv]
            assertConstraint $ TCSUse (USCConditional [] (UCCSSubset (UCSet $ Set.singleton UCIn) gamma))
            assertConstraint $ TCSUse (USCConditionalInequality [] env (kx .+ ix) kx')
            return ((delayEnv ix $ Prelude.foldr Map.delete tenv vs) .: (a, TChannel gamma ix ts), kx')
        _ -> fail "invalid simple types"

inferProc env@(vphi, phi) senv (RepInputP a vs p) =
    case Map.lookup a senv of
        Just st@(STServ is sts) -> do
            (tenv, kx) <- inferProc (vphi `Set.union` is, phi) (Map.fromList (Prelude.zip vs sts) `Map.union` senv) p
            TServ ix _ gamma kx'' ts <- freshType vphi st
            kx' <- freshTemplate vphi
            let tenv' = Map.fromList $ (a, TServ ix is gamma kx'' ts) : Prelude.zip vs ts
            assertConstraints $ Set.fromList [TCSConditionalSubsumption [] (vphi `Set.union` is, phi) (tenv' ! w) (tenv ! w) | w <- Map.keys tenv', Map.member w tenv]
            let tenv'' = Prelude.foldr Map.delete tenv vs
            assertConstraints $ Set.fromList [TCSInvariant env t | t <- Map.elems tenv'']
            assertConstraint $ TCSUse (USCConditional [] (UCCSSubset (UCSet $ Set.singleton UCIn) gamma))
            assertConstraint $ (TCSUse (USCIndex (ICSEqual kx kx'')))
            assertConstraint $ TCSUse (USCConditionalInequality [] env ix kx')
            return ((delayEnv ix tenv'') .: (a, TServ ix is gamma kx'' ts), kx') 


        _ -> fail "invalid simple types"

inferProc env@(vphi, _) senv (OutputP a es) = do
    (tenvs, ss) <- mapM (inferExp env senv) es >>= return . unzip
    assertConstraints $ fst (Prelude.foldr (\tenv' (cs, tenv'') -> (cs `Set.union` (tenv' .~ tenv''), tenv' `Map.union` tenv'')) (Set.empty, Map.empty) tenvs)
    case Map.lookup a senv of
        Just st@(STChannel sts) -> do
            TChannel gamma ix ts <- freshType vphi st
            kx <- freshTemplate vphi
            assertConstraints $ Set.fromList [TCSConditionalSubsumption [] env s t | (s, t) <- Prelude.zip ss ts]
            assertConstraint $ TCSUse (USCConditional [] (UCCSSubset (UCSet $ Set.singleton UCOut) gamma))
            assertConstraint $ TCSUse (USCConditionalInequality [] env ix kx)
            return ((delayEnv ix $ Prelude.foldr Map.union Map.empty tenvs) .: (a, TChannel gamma ix ts), kx)


        Just st@(STServ is sts) -> do
            TServ ix is gamma kx' ts <- freshType vphi st
            kx <- freshTemplate vphi
            jxs <- sequence [freshTemplate vphi | _ <- [0 .. Set.size is - 1]]
            ss' <- mapM (freshType vphi) sts
            assertConstraints $ Set.fromList [TCSConditionalSubsumption [] env s s' | (s, s') <- Prelude.zip ss ss']
            assertConstraints $ Set.fromList [TCSConditionalSubsumption [] env s' (typeSubst (Map.fromList $ Prelude.zip (Set.toList is) jxs) t) | (s', t) <- Prelude.zip ss' ts]
            assertConstraint $ TCSUse (USCConditionalInequality [] env (ix .+ indexSubst kx' (Map.fromList $ Prelude.zip (Set.toList is) jxs)) kx)
            assertConstraint $ TCSUse (USCConditional [] (UCCSSubset (UCSet $ Set.singleton UCOut) gamma))
            return ((delayEnv ix $ Prelude.foldr Map.union Map.empty tenvs) .: (a, TServ ix is gamma kx' ts), kx)
        
        _ -> fail "invalid simple types"
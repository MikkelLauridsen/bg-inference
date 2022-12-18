{-# LANGUAGE FlexibleInstances #-}

module TypeInference
( inferTypes
, TypeEnv
, SimpleEnv
) where

import Constraints
import Control.Exception
import Control.Monad.Except
import Control.Monad.State
import Control.Monad (when, mapM)
import Control.Monad.Extra (ifM, whenM)
import Data.Set as Set
import Data.Map as Map
import Index
import PiCalculus
import Types
import IndexConstraintSolving

data InferState = InferState
  { nextCapabVar :: Int,
    nextCoeffVar :: Int,
    typeConstraints :: Set TypeConstraint,
    isTimeInvariant :: Bool
  }

type Infer a = StateT InferState (Either (InferState, String)) a

instance MonadFail (Either (InferState, String)) where
  fail serr = Left (initState, serr)

type SimpleEnv = Map Var SimpleType

type TypeEnv = Map Var Type


initState = InferState { nextCapabVar = 0, nextCoeffVar = 0, typeConstraints = Set.empty, isTimeInvariant = False }


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
freshType vphi (STVar _) = fail "Simple type not instantiated"
freshType vphi (STNat) = do
    jx <- freshTemplate vphi
    return $ TNat zeroIndex jx

freshType vphi (STChannel sts) = do
    gamma <- freshCapabVar
    ix <- freshTemplate vphi
    ts <- sequence $ Prelude.map (freshType vphi) sts
    return $ TChannel (UCVar gamma) ix ts

freshType vphi (STServ is sts) = do
    isTimeInvariant <- isTimeInvariantM
    if isTimeInvariant
        then do
            gamma <- freshCapabVar
            kx <- freshTemplate $ vphi `Set.union` is
            s <- get
            (ts, _) <- Prelude.foldr freshMessageType (return ([], Set.toList is)) sts
            return $ TInvar is (UCVar gamma) kx ts
        else do
            gamma <- freshCapabVar
            ix <- freshTemplate $ vphi `Set.difference` is
            kx <- freshTemplate $ vphi `Set.union` is
            s <- get
            (ts, _) <- Prelude.foldr freshMessageType (return ([], Set.toList is)) sts
            return $ TServ ix is (UCVar gamma) kx ts
    where
        freshMessageType STNat curr = do 
            (ss, i : js') <- curr
            return (TNat (Index (Map.empty, COENumeral 0)) (Index (Map.singleton i (COENumeral 1), COENumeral 0)) : ss, js')
        freshMessageType st curr = do 
            (ss, js) <- curr
            t <- freshType (vphi `Set.union` is) st
            return (t : ss, js)


(.~) :: TypeEnv -> TypeEnv -> Set TypeConstraint
(.~) tenv tenv' = Set.fromList [TCSEqual (tenv ! v) (tenv' ! v) | v <- Set.toList (Map.keysSet tenv `Set.intersection` Map.keysSet tenv')]


assertConstraints :: Set TypeConstraint -> Infer ()
assertConstraints cs = get >>= (\s -> put s{ typeConstraints = typeConstraints s `Set.union` cs })


assertConstraint :: TypeConstraint -> Infer ()
assertConstraint = assertConstraints . Set.singleton


zeroIndex :: Index
zeroIndex = Index (Map.empty, COENumeral 0) 


oneIndex :: Index
oneIndex = Index (Map.empty, COENumeral 1) 


nIndex :: Integer -> Index
nIndex n = Index (Map.empty, COENumeral n)


delay :: Index -> Type -> Type
delay jx (TChannel sigma ix ts) = TChannel sigma (ix .+ jx) ts
delay jx (TServ ix is sigma kx ts) = TServ (ix .+ jx) is sigma kx ts
delay _ t = t


delayEnv :: Index -> TypeEnv -> TypeEnv
delayEnv jx = Map.map (delay jx)


delayEnvServ :: IndexVarConstraintEnv -> Index -> TypeEnv -> Infer TypeEnv
delayEnvServ env@(vphi, _) ix = mapM $ \t ->
    case t of
        TServ _ is sigma kx ts -> do
            jx <- freshTemplate vphi
            TServ _ _ sigma' kx' ts' <- freshType vphi $ mkSimpleType t
            assertConstraint $ TCSUse (USCConditionalInequality [] env jx ix)
            assertConstraint $ TCSConditionalSubsumption [] env (TServ jx is sigma' kx' ts') $ TServ jx is sigma kx ts            
            return $ TServ jx is sigma' kx' ts'

        _ -> return t 


mkSimpleType :: Type -> SimpleType
mkSimpleType (TNat _ _) = STNat
mkSimpleType (TChannel _ _ ts) = STChannel $ Prelude.map mkSimpleType ts
mkSimpleType (TServ _ is _ _ ts) = STServ is $ Prelude.map mkSimpleType ts


inferTypes :: IndexVarConstraintEnv -> SimpleEnv -> Proc -> Either String (TypeEnv, Set TypeConstraint, Index)
inferTypes env senv p =
    case runStateT (inferProc env senv p >>= \(tenv, kx) -> assertConstraint (TCSUse (USCConditionalInequality [] env zeroIndex kx)) >> return (tenv, kx)) initState of
        Left (_, serr) -> Left serr
        Right ((tenv, kx), s) -> Right (tenv, typeConstraints s, kx)


inferExp :: IndexVarConstraintEnv -> SimpleEnv -> Exp -> Infer (TypeEnv, Type)
inferExp env@(vphi, _) senv ZeroE = do 
    jx <- freshTemplate vphi
    assertConstraint $ TCSUse (USCConditionalInequality [] env zeroIndex jx)
    return (Map.empty, TNat zeroIndex jx)

inferExp env@(vphi, _) senv (VarE v) = 
    case Map.lookup v senv of
        Just st -> do 
            t <- freshType vphi st 
            assertSizeConstraints t
            return (Map.singleton v t, t)
        _ -> fail $ "name '" ++ show v ++ "' is free"
    where
        assertSizeConstraints (TNat ix jx) = do 
            assertConstraint $ TCSUse (USCIndex (ICSEqual zeroIndex ix))
            assertConstraint $ TCSUse (USCConditionalInequality [] env ix jx)
        
        assertSizeConstraints (TChannel _ _ ts) = forM_ ts assertSizeConstraints
        assertSizeConstraints (TServ _ _ _ _ ts) = forM_ ts assertSizeConstraints

inferExp env@(vphi, _) senv e@(SuccE _) = do
    let (n, e') = collectSuccessors e
    (tenv, t) <- inferExp env senv e'
    jx <- freshTemplate vphi
    jx' <- freshTemplate vphi
    assertConstraint $ TCSEqual t (TNat zeroIndex jx)
    assertConstraint $ TCSConditionalSubsumption [] env (TNat zeroIndex (jx .+ nIndex n)) (TNat zeroIndex  jx')
    return (tenv, TNat zeroIndex jx')
    where
        collectSuccessors (SuccE e') =
            let (n, e'') = collectSuccessors e'
            in (n + 1, e'')
        collectSuccessors e'' = (0, e'')


inferProc :: IndexVarConstraintEnv -> SimpleEnv -> Proc -> Infer (TypeEnv, Index)
inferProc env senv (RestrictP a st p) = do
    (tenv, kx) <- inferProc env (senv .: (a, st)) p
    return (Map.delete a tenv, kx)

inferProc env@(vphi, _) senv NilP = do
    kx <- freshTemplate vphi
    assertConstraint $ TCSUse (USCConditionalInequality [] env zeroIndex kx)
    return (Map.empty, kx)

inferProc env senv (p :|: q) = do
    (tenv, kx) <- inferProc env senv p
    (tenv', kx') <- inferProc env senv q
    assertConstraint $ (TCSUse (USCIndex (ICSEqual kx kx')))
    assertConstraints $ tenv .~ tenv'
    return (tenv `Map.union` tenv', kx)

inferProc env@(vphi, _) senv (TickP p) = do
    (tenv, kx) <- inferProc env senv p
    kx' <- freshTemplate vphi
    assertConstraint $ TCSUse (USCConditionalInequality [] env (kx .+ oneIndex) kx')
    return (delayEnv oneIndex tenv, kx')

inferProc env@(vphi, phi) senv (MatchNatP e p x q) = do
    (tenv, TNat ix jx) <- inferExp (vphi, phi) senv e
    (tenv', kx) <- inferProc (vphi, Set.insert (IVCLessEq ix zeroIndex) phi) senv p
    (tenv'', kx') <- inferProc (vphi, Set.insert (IVCLessEq oneIndex jx) phi) (senv .: (x, STNat)) q
    assertConstraint $ (TCSUse (USCIndex (ICSEqual kx kx')))
    assertConstraints $ tenv .~ tenv'
    assertConstraints $ tenv .~ tenv''
    assertConstraints $ tenv' .~ tenv''
    case Map.lookup x tenv'' of
        Just (TNat (Index (m, c)) (Index (m', c'))) -> assertConstraint $ TCSConditionalSubsumption [] env (TNat ix jx) (TNat zeroIndex (Index (m', COEAdd c' (COENumeral 1)))) -- only zeroIndex if no lowerbound..
        _ -> return ()
    return (Map.delete x $ tenv `Map.union` tenv' `Map.union` tenv'', kx)

inferProc env@(vphi, _) senv (InputP a vs p) =
    case Map.lookup a senv of
        Just st@(STChannel sts) -> do
            (tenv, kx) <- inferProc env (Map.fromList (Prelude.zip vs sts) `Map.union` senv) p
            TChannel gamma ix ts <- freshType vphi st
            kx' <- freshTemplate vphi
            let tenv' = Map.fromList $ (a, TChannel gamma ix ts) : Prelude.zip vs ts
            assertConstraint $ TCSUse (USCConditionalInequality [] env zeroIndex ix)
            assertConstraints $ Set.fromList [TCSConditionalSubsumption [] env (tenv' ! w) (tenv ! w) | w <- Map.keys tenv', Map.member w tenv]
            assertConstraint $ TCSUse (USCConditional [] (UCCSSubset (UCSet $ Set.singleton UCIn) gamma))
            assertConstraint $ TCSUse (USCConditionalInequality [] env (kx .+ ix) kx')
            return ((delayEnv ix $ Prelude.foldr Map.delete tenv vs) .: (a, TChannel gamma ix ts), kx')
        _ -> fail "invalid simple type; Expected channel type"

inferProc env@(vphi, phi) senv (RepInputP a vs p) =
    case Map.lookup a senv of
        Just st@(STServ is sts) -> do
            setTimeInvariance True
            (tenvInvar, kx) <- inferProc (vphi `Set.union` is, phi) (Map.fromList (Prelude.zip vs sts) `Map.union` senv) p
            let tenv = Map.map mapInvar tenvInvar
            setTimeInvariance False
            TServ ix _ gamma kx'' ts <- freshType vphi st
            kx' <- freshTemplate vphi
            let tenv' = Prelude.foldr Map.delete tenv vs
            assertConstraint $ TCSUse (USCConditionalInequality [] env zeroIndex ix)
            assertConstraints $ Set.fromList [TCSInvariant env t | t <- Map.elems tenv']
            assertConstraint $ TCSUse (USCConditional [] (UCCSSubset (UCSet $ Set.singleton UCIn) gamma))
            assertConstraint $ TCSUse (USCIndex (ICSEqual kx kx''))
            assertConstraint $ TCSUse (USCConditionalInequality [] env ix kx')
            assertConstraints $ Set.fromList [TCSConditionalSubsumption [] (vphi `Set.union` is, phi) t (tenv ! v) | (v, t) <- Prelude.zip vs ts, Map.member v tenv]
            case Map.lookup a tenv of
                Just (TServ _ _ gamma' kx3 ts') -> do
                    assertConstraint $ TCSUse (USCConditional [] (UCCSSubset gamma' gamma))
                    assertConstraint $ TCSUse (USCConditionalInequality [] (vphi `Set.union` is, phi) kx'' kx3)
                    assertConstraints $ Set.fromList [TCSConditionalSubsumption [] (vphi `Set.union` is, phi) t' t | (t, t') <- Prelude.zip ts ts']
                _ -> return ()
            tenv'' <- delayEnvServ env ix tenv'
            -- TODO: trace tenv'' and tenv';; let's see how server 'a' is 'mapped' (also trace the constraints added by delayEnvServ;; we should see a clear connection ..)
            return (tenv'' .: (a, TServ ix is gamma kx'' ts), kx') 


        _ -> fail "invalid simple type; Expected server type"
    where
        mapInvar (TInvar is gamma kx ts) = TServ zeroIndex is gamma kx ts
        mapInvar t = t

inferProc env@(vphi, _) senv (OutputP a es) = do
    (tenvs, ss) <- mapM (inferExp env senv) es >>= return . unzip
    assertConstraints $ fst (Prelude.foldr (\tenv' (cs, tenv'') -> (cs `Set.union` (tenv' .~ tenv''), tenv' `Map.union` tenv'')) (Set.empty, Map.empty) tenvs)
    case Map.lookup a senv of
        Just st@(STChannel sts) -> do
            TChannel gamma ix ts <- freshType vphi st
            kx <- freshTemplate vphi
            assertConstraint $ TCSUse (USCConditionalInequality [] env zeroIndex ix)
            assertConstraints $ Set.fromList [TCSConditionalSubsumption [] env s t | (s, t) <- Prelude.zip ss ts]
            assertConstraint $ TCSUse (USCConditional [] (UCCSSubset (UCSet $ Set.singleton UCOut) gamma))
            assertConstraint $ TCSUse (USCConditionalInequality [] env ix kx)
            return ((delayEnv ix $ Prelude.foldr Map.union Map.empty tenvs) .: (a, TChannel gamma ix ts), kx)

        Just st@(STServ is sts) -> do
            tserv <- freshType vphi st
            case tserv of
                TInvar is gamma kx' ts -> do
                    kx <- freshTemplate vphi
                    ss' <- mapM (freshType vphi) sts
                    let subst = instantiate (Set.toList is) ts ss' 
                    assertConstraints $ Set.fromList [TCSConditionalSubsumption [] env s s' | (s, s') <- Prelude.zip ss ss']
                    assertConstraints $ Set.fromList [TCSEqual s' (typeSubst subst t) | (s', t) <- Prelude.zip ss' ts]
                    assertConstraint $ TCSUse (USCConditionalInequality [] env (indexSubst kx' subst) kx)
                    assertConstraint $ TCSUse (USCConditional [] (UCCSSubset (UCSet $ Set.singleton UCOut) gamma))
                    assertConstraint $ TCSUse (USCConditionalInequality [] env zeroIndex kx')
                    return (Prelude.foldr Map.union Map.empty tenvs .: (a, TInvar is gamma kx' ts), kx)

                TServ ix is gamma kx' ts -> do
                    kx <- freshTemplate vphi
                    ss' <- mapM (freshType vphi) sts
                    let subst = instantiate (Set.toList is) ts ss' 
                    assertConstraints $ Set.fromList [TCSConditionalSubsumption [] env s s' | (s, s') <- Prelude.zip ss ss']
                    assertConstraints $ Set.fromList [TCSEqual s' (typeSubst subst t) | (s', t) <- Prelude.zip ss' ts]
                    assertConstraint $ TCSUse (USCConditionalInequality [] env (ix .+ indexSubst kx' subst) kx)
                    assertConstraint $ TCSUse (USCConditional [] (UCCSSubset (UCSet $ Set.singleton UCOut) gamma))
                    assertConstraint $ TCSUse (USCConditionalInequality [] env zeroIndex kx')
                    assertConstraint $ TCSUse (USCConditionalInequality [] env zeroIndex ix)
                    return ((delayEnv ix $ Prelude.foldr Map.union Map.empty tenvs) .: (a, TServ ix is gamma kx' ts), kx)
        
        _ -> fail "invalid simple type; Expected channel type or server type"


instantiate :: [IndexVar] -> [Type] -> [Type] -> Map IndexVar Index
instantiate (i : is') ((TNat _ _) : ts') ((TNat _ jx) : ss') = Map.singleton i jx `Map.union` instantiate is' ts' ss'
instantiate is (t : ts') (s : ss') = instantiate is ts' ss'
instantiate [] [] [] = Map.empty


isTimeInvariantM :: Infer Bool
isTimeInvariantM = get >>= return . isTimeInvariant

setTimeInvariance :: Bool -> Infer ()
setTimeInvariance b = get >>= (\s -> put $ s{ isTimeInvariant = b })
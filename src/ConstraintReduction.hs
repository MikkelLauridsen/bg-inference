module ConstraintReduction
  ( reduceTypeConstraints,
    solveUseConstraints,
  )
where

import Constraints
import Data.Map as Map
import Data.Set as Set
import Free
import Index
import Types

type UseValuation = Map CapabVar (Set UseCapabilityType)

reduceTypeConstraints :: Set TypeConstraint -> Set UseConstraint
reduceTypeConstraints tcs = aux (tcs, Set.empty)
  where
    aux (tcs', ucs')
      | Set.null tcs' = ucs'
      | otherwise = aux $ Set.foldr reduceTypeConstraint (Set.empty, ucs') tcs'

    reduceTypeConstraint (TCSEqual (TNat ix jx) (TNat ix' jx')) (tcs', ucs') = (tcs', ucs' `Set.union` Set.fromList [USCIndex (ICSEqual ix ix'), USCIndex (ICSEqual jx jx')])
    reduceTypeConstraint (TCSEqual (TChannel sigma ix ts) (TChannel sigma' jx ss)) (tcs', ucs') = (tcs' `Set.union` tcs'', ucs' `Set.union` ucs'')
      where
        tcs'' = Set.fromList [TCSEqual t s | (t, s) <- Prelude.zip ts ss]
        ucs'' = Set.fromList [USCIndex (ICSEqual ix jx), USCConditional [] (UCCSSubset sigma sigma'), USCConditional [] (UCCSSubset sigma' sigma)]

    -- quantified index variables should match, considering simple type inference
    reduceTypeConstraint (TCSEqual (TServ ix _ sigma kx ts) (TServ jx _ sigma' kx' ss)) (tcs', ucs') = (tcs' `Set.union` tcs'', ucs' `Set.union` ucs'')
      where
        tcs'' = Set.fromList [TCSEqual t s | (t, s) <- Prelude.zip ts ss]
        ucs'' = Set.fromList [USCIndex (ICSEqual ix jx), USCIndex (ICSEqual kx kx'), USCConditional [] (UCCSSubset sigma sigma'), USCConditional [] (UCCSSubset sigma' sigma)]
    reduceTypeConstraint (TCSInvariant env (TNat _ _)) (tcs', ucs') = (tcs', ucs')
    reduceTypeConstraint (TCSInvariant env (TChannel _ _ _)) (tcs', ucs') = (Set.empty, Set.singleton (USCIndex ICSFalse))
    reduceTypeConstraint (TCSInvariant env@(vphi, _) (TServ ix _ sigma _ _)) (tcs', ucs') = (tcs', ucs' `Set.union` ucs'')
      where
        ucs'' = Set.fromList [USCIndex (ICSLessEq env ix (zeroIndex vphi)), USCConditional [] (UCCSSubset sigma (UCSet $ Set.singleton UCOut))]
    reduceTypeConstraint (TCSConditionalSubsumption cgammas env (TNat ix jx) (TNat ix' jx')) (tcs', ucs') = (tcs', ucs' `Set.union` ucs'')
      where
        ucs'' = Set.fromList [USCConditionalInequality cgammas env ix' ix, USCConditionalInequality cgammas env jx jx']
    reduceTypeConstraint (TCSConditionalSubsumption cgammas env (TChannel sigma ix ts) (TChannel sigma' jx ss)) (tcs', ucs') = (tcs' `Set.union` tcs'', ucs' `Set.union` ucs'')
      where
        tcs'' =
          Set.fromList
            ( [TCSConditionalSubsumption (UCCSSubset sigma (UCSet (Set.singleton UCIn)) : cgammas) env t s | (t, s) <- Prelude.zip ts ss]
                ++ [TCSConditionalSubsumption (UCCSSubset sigma (UCSet (Set.singleton UCOut)) : cgammas) env s t | (t, s) <- Prelude.zip ts ss]
            )
        ucs'' = Set.fromList [USCConditional cgammas (UCCSSubset sigma' sigma), USCIndex (ICSEqual ix jx)]

    -- quantified index variables should match, considering simple type inference
    reduceTypeConstraint (TCSConditionalSubsumption cgammas (vphi, phi) (TServ ix is sigma kx ts) (TServ jx _ sigma' kx' ss)) (tcs', ucs') = (tcs' `Set.union` tcs'', ucs' `Set.union` ucs'')
      where
        tcs'' =
          Set.fromList
            ( [TCSConditionalSubsumption (UCCSSubset sigma (UCSet (Set.singleton UCIn)) : cgammas) (vphi `Set.union` is, phi) t s | (t, s) <- Prelude.zip ts ss]
                ++ [TCSConditionalSubsumption (UCCSSubset sigma (UCSet (Set.singleton UCOut)) : cgammas) (vphi `Set.union` is, phi) s t | (t, s) <- Prelude.zip ts ss]
            )
        ucs'' =
          Set.fromList
            [ USCConditional cgammas (UCCSSubset sigma' sigma),
              USCIndex (ICSEqual ix jx),
              USCConditionalInequality (UCCSSubset sigma (UCSet (Set.singleton UCIn)) : cgammas) (vphi `Set.union` is, phi) kx kx',
              USCConditionalInequality (UCCSSubset sigma (UCSet (Set.singleton UCOut)) : cgammas) (vphi `Set.union` is, phi) kx' kx
            ]
    reduceTypeConstraint (TCSUse uc) (tcs', ucs') = (tcs', Set.insert uc ucs')
    reduceTypeConstraint _ _ = (Set.empty, Set.singleton (USCIndex ICSFalse))

solveUseConstraints :: Set UseConstraint -> (Set IndexConstraint, UseValuation)
solveUseConstraints ucs
  | Set.foldr ((&&) . satisfiesUC f) True ucs = (Set.foldr (Set.union . applyValuation) Set.empty ucs, f)
  | otherwise = (Set.singleton ICSFalse, Map.empty)
  where
    f = mkUseValuation ucs

    applyValuation (USCConditionalInequality cgammas env ix jx) | satisfiesAll f cgammas = Set.singleton $ ICSLessEq env ix jx
    applyValuation (USCIndex cindex) = Set.singleton cindex
    applyValuation _ = Set.empty

mkUseValuation :: Set UseConstraint -> UseValuation
mkUseValuation ucs = aux $ Map.fromList (Prelude.zip (Set.toList $ fuv ucs) (Prelude.repeat Set.empty))
  where
    aux f
      | f == f' = f
      | otherwise = aux f'
      where
        f' = Set.foldr satisfyConstraint f ucs

    satisfyConstraint (USCConditional cgammas (UCCSSubset (UCVar gamma) (UCVar gamma'))) f | f `satisfiesAll` cgammas = Map.adjust ((f ! gamma) `Set.union`) gamma' f
    satisfyConstraint (USCConditional cgammas (UCCSSubset (UCSet sigma) (UCVar gamma'))) f | f `satisfiesAll` cgammas = Map.adjust (sigma `Set.union`) gamma' f
    satisfyConstraint _ f = f

satisfies f (UCCSSubset (UCVar gamma) (UCVar gamma')) = (f ! gamma) `Set.isSubsetOf` (f ! gamma')
satisfies f (UCCSSubset (UCVar gamma) (UCSet sigma')) = (f ! gamma) `Set.isSubsetOf` sigma'
satisfies f (UCCSSubset (UCSet sigma) (UCVar gamma')) = sigma `Set.isSubsetOf` (f ! gamma')
satisfies f (UCCSSubset (UCSet sigma) (UCSet sigma')) = sigma `Set.isSubsetOf` sigma'

satisfiesAll f = Prelude.foldr ((&&) . satisfies f) True

satisfiesUC f (USCConditional cgammas cgamma) = not (satisfiesAll f cgammas) || satisfies f cgamma
satisfiesUC f _ = True

zeroIndex :: Set IndexVar -> Index
zeroIndex vphi = Index (Map.fromList $ Prelude.zip (Set.toList vphi) (Prelude.map COENumeral [0, 0 ..]), COENumeral 0)
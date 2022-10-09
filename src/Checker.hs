module Checker(
  applyConstraintSubst
, ConstraintSubst
) where

import Types
import Constraints
import Data.Map as Map
import Data.Set as Set
import Index

type ConstraintSubst = (UseValuation, Map CoeffVar Integer)


applyConstraintSubstList :: ConstraintSubst -> [TypeConstraint] -> [TypeConstraint]
applyConstraintSubstList subst = Prelude.map (applyConstraintSubst subst) 


applyConstraintSubst :: ConstraintSubst -> TypeConstraint -> TypeConstraint
applyConstraintSubst subst (TCSEqual t s) = TCSEqual (applyConstraintSubstType subst t) (applyConstraintSubstType subst s)
applyConstraintSubst subst (TCSInvariant (vars, indexVarConstraints) t) = TCSInvariant env' (applyConstraintSubstType subst t)
    where
        env' = (vars, Set.map (applyConstraintSubstIndexVarConstraint subst) indexVarConstraints)

applyConstraintSubst subst (TCSConditionalSubsumption useConstraints (vars, indexVarConstraints) t s) = TCSConditionalSubsumption useConstraints' env' t' s'
    where
        useConstraints' = Prelude.map (applyConstraintSubstUseConstraint subst) useConstraints
        env' = (vars, Set.map (applyConstraintSubstIndexVarConstraint subst) indexVarConstraints)
        t' = (applyConstraintSubstType subst t)
        s' = (applyConstraintSubstType subst t)

applyConstraintSubst subst (TCSUse useConstraint) = TCSUse $ applyConstraintSubstUse subst useConstraint


applyConstraintSubstUse subst (USCConditionalInequality capabConstraints (vars, indexVarConstraints) ix1 ix2) = USCConditionalInequality capabConstraints' env' ix1' ix2'
    where
        capabConstraints' = Prelude.map (applyConstraintSubstUseConstraint subst) capabConstraints
        env' = (vars, Set.map (applyConstraintSubstIndexVarConstraint subst) indexVarConstraints)
        ix1' = applyConstraintSubstIndex subst ix1
        ix2' = applyConstraintSubstIndex subst ix2

applyConstraintSubstUse subst (USCConditional capabConstraints capabConstraint) = USCConditional capabConstraints' capabConstraint'
    where
        capabConstraints' = Prelude.map (applyConstraintSubstUseConstraint subst) capabConstraints
        capabConstraint' = applyConstraintSubstUseConstraint subst capabConstraint

applyConstraintSubstUse subst (USCIndex indexConstraint) = USCIndex $ applyConstraintSubstIndexConstraint subst indexConstraint


applyConstraintSubstIndexConstraint subst (ICSEqual ix1 ix2) = ICSEqual ix1' ix2'
    where
        ix1' = applyConstraintSubstIndex subst ix1
        ix2' = applyConstraintSubstIndex subst ix2

applyConstraintSubstIndexConstraint subst (ICSLessEq (vars, indexVarConstraints) ix1 ix2) = ICSLessEq env' ix1' ix2'
    where
        env' = (vars, Set.map (applyConstraintSubstIndexVarConstraint subst) indexVarConstraints)
        ix1' = applyConstraintSubstIndex subst ix1
        ix2' = applyConstraintSubstIndex subst ix2

applyConstraintSubstIndexConstraint _ indexConstraint = indexConstraint


applyConstraintSubstIndexVarConstraint subst (IVCLessEq ix1 ix2) = IVCLessEq (applyConstraintSubstIndex subst ix1) (applyConstraintSubstIndex subst ix2)


applyConstraintSubstUseConstraint subst (UCCSSubset useCapa1 useCapa2) = UCCSSubset useCapa1' useCapa2'
    where
        useCapa1' = applyConstraintSubstUseCapability subst useCapa1
        useCapa2' = applyConstraintSubstUseCapability subst useCapa2

applyConstraintSubstUseCapability (useValuation, _) (UCVar useVar) =
    case Map.lookup useVar useValuation of
        Just capab -> UCSet capab
        _ -> UCVar useVar

applyConstraintSubstUseCapability _ inCapa = inCapa 

applyConstraintSubstType (useValuation, coeffMap) t = (applyISubstType coeffMap (applyUseValuation useValuation t))

applyConstraintSubstIndex subst (Index (coeffs, coeff)) = Index (coeffs', coeff')
    where
        coeffs' = Map.map (applyConstraintSubstCoefficient subst) coeffs
        coeff' = applyConstraintSubstCoefficient subst coeff 


applyConstraintSubstCoefficient subst@(_, coeffMap) c =
    case c of
        (COEVar coeffVar) -> 
            case Map.lookup coeffVar coeffMap of
                Just n -> COENumeral n
                _ -> COEVar coeffVar

        COEAdd c1 c2 -> COEAdd (applyConstraintSubstCoefficient subst c1) (applyConstraintSubstCoefficient subst c2)
        COEMul c1 c2 -> COEAdd (applyConstraintSubstCoefficient subst c1) (applyConstraintSubstCoefficient subst c2)
        COESub c1 c2 -> COEAdd (applyConstraintSubstCoefficient subst c1) (applyConstraintSubstCoefficient subst c2)
        COEDiv c1 c2 -> COEAdd (applyConstraintSubstCoefficient subst c1) (applyConstraintSubstCoefficient subst c2)
        _ -> c


module Free (
  Free (..)
) where

import Data.Set as Set
import Data.Map as Map
import Index
import Types
import Constraints


class Free a where

    ftv :: a -> Set CoeffVar -- free coefficient variables

    fuv :: a -> Set CapabVar -- free use-variables

    fiv :: a -> Set IndexVar -- free index variables


instance (Free a) => Free (Set a) where

    ftv = Set.foldr (Set.union . ftv) Set.empty

    fuv = Set.foldr (Set.union . fuv) Set.empty

    fiv = Set.foldr (Set.union . fiv) Set.empty


instance (Free a) => Free [a] where

    ftv = Prelude.foldr (Set.union . ftv) Set.empty

    fuv = Prelude.foldr (Set.union . fuv) Set.empty

    fiv = Prelude.foldr (Set.union . fiv) Set.empty


instance (Free k, Free a) => Free (Map k a) where

    ftv m = ftv (Map.keys m) `Set.union` ftv (Map.elems m)

    fuv m = fuv (Map.keys m) `Set.union` fuv (Map.elems m)

    fiv m = fiv (Map.keys m) `Set.union` fiv (Map.elems m)


instance (Free a, Free b) => Free (a, b) where

    ftv (x, y) = ftv x `Set.union` ftv y

    fuv (x, y) = fuv x `Set.union` fuv y

    fiv (x, y) = fiv x `Set.union` fiv y


instance Free CoeffVar where

    ftv = Set.singleton

    fuv _ = Set.empty

    fiv _ = Set.empty


instance Free CapabVar where

    ftv _ = Set.empty

    fuv = Set.singleton

    fiv _ = Set.empty


instance Free IndexVar where

    ftv _ = Set.empty

    fuv _ = Set.empty

    fiv = Set.singleton


instance Free Coefficient where

  ftv (COEVar alpha) = Set.singleton alpha
  ftv (COEAdd calpha calpha') = ftv calpha `Set.union` ftv calpha'
  ftv (COEMul calpha calpha') = ftv calpha `Set.union` ftv calpha'
  ftv _ = Set.empty

  fuv _ = Set.empty

  fiv _ = Set.empty


instance Free Type where

  ftv (TNat ix jx) = ftv ix `Set.union` ftv jx
  ftv (TChannel sigma ix ts) = ftv ix `Set.union` ftv ts
  ftv (TServ ix _ sigma kx ts) = ftv ix `Set.union` ftv kx `Set.union` ftv ts

  fuv (TChannel sigma _ ts) = fuv sigma `Set.union` fuv ts
  fuv (TServ _ _ sigma _ ts) = fuv sigma `Set.union` fuv ts
  fuv _ = Set.empty

  fiv (TNat ix jx) = fiv ix `Set.union` fiv jx
  fiv (TChannel _ ix ts) = fiv ix `Set.union` fiv ts
  fiv (TServ ix vphi sigma kx ts) = Set.difference (fiv ix `Set.union` fiv kx `Set.union` fiv ts) vphi


instance Free UseCapability where
  
  ftv _ = Set.empty
  
  fuv (UCVar gamma) = Set.singleton gamma
  fuv _ = Set.empty

  fiv _ = Set.empty


instance Free TypeConstraint where

  ftv (TCSEqual t s) = ftv t `Set.union` ftv s
  ftv (TCSInvariant (_, phi) t) = ftv phi `Set.union` ftv t
  ftv (TCSConditionalSubsumption cgammas (_, phi) t s) = ftv cgammas `Set.union` ftv phi `Set.union` ftv t `Set.union` ftv s
  ftv (TCSUse uc) = ftv uc

  fuv (TCSEqual t s) = fuv t `Set.union` fuv s
  fuv (TCSInvariant _ t) = fuv t
  fuv (TCSConditionalSubsumption cgammas _ t s) = fuv cgammas `Set.union` fuv t `Set.union` fuv s
  fuv (TCSUse uc) = fuv uc

  fiv (TCSEqual t s) = fiv t `Set.union` fiv s
  fiv (TCSInvariant (vphi, _) _) = vphi
  fiv (TCSConditionalSubsumption _ (vphi, _) _ _) = vphi
  fiv (TCSUse uc) = fiv uc 


instance Free UseConstraint where

  ftv (USCConditionalInequality uccs (_, phi) ix jx) = ftv uccs `Set.union` ftv phi `Set.union` ftv ix `Set.union` ftv jx
  ftv (USCConditional uccs ucc) = ftv uccs `Set.union` ftv ucc
  ftv (USCIndex calpha) = ftv calpha 

  fuv (USCConditionalInequality uccs _ _ _) = fuv uccs
  fuv (USCConditional uccs ucc) = fuv uccs `Set.union` fuv ucc 
  fuv _ = Set.empty

  fiv (USCConditionalInequality _ (vphi, _) _ _) = vphi
  fiv (USCIndex calpha) = fiv calpha
  fiv _ = Set.empty


instance Free IndexConstraint where

  ftv (ICSLessEq (_, phi) ix jx) = ftv phi `Set.union` ftv ix `Set.union` ftv jx
  ftv _ = Set.empty

  fuv _ = Set.empty

  fiv (ICSLessEq (vphi, _) _ _) = vphi
  fiv _ = Set.empty


instance Free UseCapabilityConstraint where

  ftv (UCCSSubset gamma gamma') = ftv gamma `Set.union` ftv gamma'

  fuv (UCCSSubset gamma gamma') = fuv gamma `Set.union` fuv gamma'

  fiv _ = Set.empty


instance Free IndexVarConstraint where

    ftv (IVCLessEq ix jx) = ftv ix `Set.union` ftv jx

    fuv _ = Set.empty

    fiv (IVCLessEq ix jx) = fiv ix `Set.union` fiv jx


instance Free Index where

    ftv (Index pair) = ftv pair

    fuv (Index pair) = fuv pair

    fiv (Index pair) = fiv pair
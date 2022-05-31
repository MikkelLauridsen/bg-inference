module Engine
  ( inferBound,
  )
where

import ConstraintReduction
import Constraints
import Data.Set as Set
import Index
import IndexConstraintSolving
import Inference
import PiCalculus
import TypeInference
import Types

inferBound :: Int -> IndexVarConstraintEnv -> SimpleEnv -> Proc -> IO (Either String Index)
inferBound ivarsPerServer env stenv p =
  case inferSimpleTypes ivarsPerServer p of -- TODO: extend with stenv
    Left serr -> return $ Left serr
    Right substST -> do
      let p' = applySTVSubst substST p
      case inferTypes env stenv p' of
        Left serr -> return $ Left serr
        Right (tenv, cs, kx) -> do
          let reducedConstraints = reduceTypeConstraints cs
          let (cs', _) = solveUseConstraints reducedConstraints
          res <- solveIndexConstraints $ Set.toList cs'
          case res of
            Left serr -> return $ Left serr
            Right substI -> return $ Right (applyISubst substI kx)

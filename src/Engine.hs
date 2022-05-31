module Engine
( inferBound

) where

import PiCalculus
import Index
import Types
import Inference
import TypeInference
import ConstraintReduction
import IndexConstraintSolving
import Data.Set as Set


inferBound :: Int -> IndexVarConstraintEnv -> SimpleEnv -> Proc -> IO (Either String Index)
inferBound ivarsPerServer env stenv p =
    case inferSimpleTypes ivarsPerServer p of -- TODO: extend with stenv
        Left serr -> return $ Left serr
        Right substST -> do
            let p' = applySTVSubst substST p
            case inferTypes env stenv p' of
                Left serr -> return $ Left serr
                Right (tenv, cs, kx) -> do
                    let (cs', _) = solveUseConstraints $ reduceTypeConstraints cs
                    Right substI <- solveIndexConstraints $ Set.toList cs'
                    return $ Right (applyISubst substI kx)


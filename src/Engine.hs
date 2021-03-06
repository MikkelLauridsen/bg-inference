module Engine
  ( inferBound,
    inferBoundVerbose,
  )
where

import ConstraintReduction
import Constraints
import Data.Set as Set
import Data.Map as Map
import Index
import IndexConstraintSolving
import Inference
import PiCalculus
import TypeInference
import Types

inferBound :: Int -> IndexVarConstraintEnv -> SimpleEnv -> Proc -> IO (Either String Index)
inferBound ivarsPerServer env stenv p =
  case inferSimpleTypes ivarsPerServer False stenv p of -- TODO: extend with stenv
    Left serr -> return $ Left serr
    Right substST -> do
      let p' = applySTVSubst substST p
      case inferTypes env stenv p' of
        Left serr -> return $ Left serr
        Right (tenv, cs, kx) -> do
          let reducedConstraints = reduceTypeConstraints cs
          let (cs', _) = solveUseConstraints reducedConstraints
          res <- solveIndexConstraints Set.empty (Set.toList cs') (Just kx)
          case res of
            Left _ -> do
              res' <- solveIndexConstraints (getPositiveCoeffVars cs') (Set.toList cs') (Just kx)
              case res' of
                Left serr -> return $ Left serr
                Right substI -> return $ Right (applyISubst substI kx)
            Right substI -> return $ Right (applyISubst substI kx)

inferBoundVerbose :: Int -> IndexVarConstraintEnv -> SimpleEnv -> Proc -> IO (Either String Index)
inferBoundVerbose ivarsPerServer env stenv p = do
  putStrLn "Process prior to inference:"
  putStrLn $ show p
  case inferSimpleTypes ivarsPerServer False stenv p of -- TODO: extend with stenv
    Left serr -> return $ Left serr
    Right substST -> do
      putStrLn "Inferred simple type substitution:"
      putStrLn $ show substST
      let p' = applySTVSubst substST p
      case inferTypes env stenv p' of
        Left serr -> return $ Left serr
        Right (tenv, cs, kx) -> do
          putStrLn "Inferred type-constraint satisfaction problem:"
          putStrLn $ showNL cs
          let reducedConstraints = reduceTypeConstraints cs
          putStrLn "Reduced use-constraint satisfaction problem:"
          putStrLn $ showNL reducedConstraints
          let (cs', f) = solveUseConstraints reducedConstraints
          putStrLn "Reduced index-constraint satisfaction problem:"
          putStrLn $ showNL cs'
          putStrLn "Resulting use-variable valuation:"
          putStrLn $ show f
          putStrLn "Resulting positive coefficient variables:"
          putStrLn $ show (getPositiveCoeffVars cs')
          res <- solveIndexConstraints Set.empty (Set.toList cs') (Just kx)
          case res of
            Left _ -> do
              res' <- solveIndexConstraints (getPositiveCoeffVars cs') (Set.toList cs') (Just kx)
              case res' of
                Left serr -> return $ Left serr
                Right substI -> do 
                  putStrLn "Resulting coefficient variable substitution:"
                  putStrLn $ show substI
                  putStrLn "Resulting complexity bound:"
                  putStrLn $ show (applyISubst substI kx)
                  putStrLn "Resulting (APPLIED) type context:"
                  putStrLn $ show (Map.map (applyUseValuation f . applyISubstType substI) tenv)
                  return $ Right (applyISubst substI kx)
            Right substI -> do 
              putStrLn "Resulting coefficient variable substitution:"
              putStrLn $ show substI
              putStrLn "Resulting complexity bound:"
              putStrLn $ show (applyISubst substI kx)
              putStrLn "Resulting (APPLIED) type context:"
              putStrLn $ show (Map.map (applyUseValuation f . applyISubstType substI) tenv)
              return $ Right (applyISubst substI kx)


showNL :: Show a => Set a -> String
showNL = Set.foldr (\el s -> show el ++ "\\\\ " ++ s) ""
module LatexPrinting 
(
  showNL, wrapGather, printRes
)
where
import Index
import Data.Map as Map
import Data.Set as Set
import Constraints
import Checker
import Types
import IndexConstraintSolving

printRes substI tenv kx f cs cs' = do
  putStrLn "Resulting coefficient variable substitution:"
  putStrLn $ wrapGather $ showMap substI
  putStrLn "Resulting complexity bound:"
  putStrLn $ wrapGather $ show (applyISubst substI kx)
  putStrLn "Resulting (APPLIED) type context:"
  putStrLn $ wrapGather $ show (Map.map (applyUseValuation f . applyISubstType substI) tenv)
  putStrLn "Type environment:"
  putStrLn $ wrapGather $ show tenv
  putStrLn "Inferred type-constraint satisfaction problem (APPLIED):"
  putStrLn $ showNL $ Set.map (applyConstraintSubst (f, substI)) cs
  putStrLn "Reduced index-constraint satisfaction problem:"
  putStrLn $ showNL cs'
  putStrLn "Over-approximated coefficient constraints:"
  putStrLn $ showNLL (Prelude.map makeComposite $ Set.toList cs')
  putStrLn "Reduced index-constraint satisfaction problem (APPLIED):"
  putStrLn $ showNLL $ Prelude.map (applyConstraintSubstIndexConstraint (f, substI)) (Set.toList cs')
  putStrLn "Over-approximated coefficient constraints (APPLIED):"
  putStrLn $ showNLL $ Prelude.map (applyConstraintSubstCompositeConstraint (f, substI)) (Prelude.map makeComposite $ Set.toList cs')
  putStrLn "-----------------"
  return $ Right (applyISubst substI kx)

--applyCoeffVarToTypeConstraint :: Map CoeffVar Integer -> TypeConstraint -> TypeConstraint
--applyCoeffVarToTypeConstraint subst (TCSEqual t1 t2) = TCSEqual (applyCoeffVarToType subst t1) (applyCoeffVarToType subst t2)


applyCoeffVarToUseConstraint :: Map CoeffVar Integer -> UseConstraint -> UseConstraint
applyCoeffVarToUseConstraint subst (USCConditionalInequality useCapConstraints env ix1 ix2)
  = USCConditionalInequality useCapConstraints env (applyCoeffVarSubstToIndex subst ix1) (applyCoeffVarSubstToIndex subst ix2)
applyCoeffVarToUseConstraint subst (USCConditional a b) = USCConditional a b
applyCoeffVarToUseConstraint subst (USCIndex iCon) = USCIndex (applyCoeffVarSubstToIndexConstraint subst iCon)


applyCoeffVarSubstToCoefficient :: Map CoeffVar Integer -> Coefficient -> Coefficient
applyCoeffVarSubstToCoefficient subst (COEVar v) = case Map.lookup v subst of
  Just i -> COENumeral i
  Nothing -> COEVar v
applyCoeffVarSubstToCoefficient subst (COENumeral i) = COENumeral i
applyCoeffVarSubstToCoefficient subst (COEAdd c1 c2) = COEAdd (applyCoeffVarSubstToCoefficient subst c1) (applyCoeffVarSubstToCoefficient subst c2)
applyCoeffVarSubstToCoefficient subst (COESub c1 c2) = COESub (applyCoeffVarSubstToCoefficient subst c1) (applyCoeffVarSubstToCoefficient subst c2)
applyCoeffVarSubstToCoefficient subst (COEMul c1 c2) = COEMul (applyCoeffVarSubstToCoefficient subst c1) (applyCoeffVarSubstToCoefficient subst c2)
applyCoeffVarSubstToCoefficient subst (COEDiv c1 c2) = COEDiv (applyCoeffVarSubstToCoefficient subst c1) (applyCoeffVarSubstToCoefficient subst c2)

applyCoeffVarSubstToIndex :: Map CoeffVar Integer -> Index -> Index
applyCoeffVarSubstToIndex subst (Index (map, bias)) = 
  Index (Map.map (applyCoeffVarSubstToCoefficient subst) map, applyCoeffVarSubstToCoefficient subst bias)

applyCoeffVarSubstToIndexConstraint :: Map CoeffVar Integer -> IndexConstraint -> IndexConstraint
applyCoeffVarSubstToIndexConstraint subst (ICSEqual ix1 ix2) = ICSEqual (applyCoeffVarSubstToIndex subst ix1) (applyCoeffVarSubstToIndex subst ix2)
applyCoeffVarSubstToIndexConstraint subst (ICSLessEq env ix1 ix2) = ICSLessEq env (applyCoeffVarSubstToIndex subst ix1) (applyCoeffVarSubstToIndex subst ix2)
applyCoeffVarSubstToIndexConstraint _ ICSFalse = ICSFalse


showNL' :: Show a => [a] -> String
showNL' = Prelude.foldr (\el s -> show el ++ "\\\\ " ++ s) ""

wrapGather :: String -> String
wrapGather s = "\\begin{gather}" ++ s ++ "\\end{gather}"

showGather :: Show a => [a] -> String
showGather s = wrapGather $ showNL' s

group :: Int -> [a] -> [[a]]
group _ [] = []
group n l
  | n > 0 = Prelude.take n l : group n (Prelude.drop n l)
  | otherwise = error "Negative or zero n"

showGathers :: Show a => [a] -> String
showGathers elems = "\\setcounter{equation}{0} " ++ Prelude.foldr (\el s -> showGather el ++ "\n" ++ s) "" groups ++ "\\newpage "
  where groups = group 49 elems

showNL :: Show a => Set a -> String
showNL = showGathers . Set.toList

showNLL :: Show a => [a] -> String
showNLL = showGathers

showMap :: (Show k, Show v) => Map k v -> String
showMap map = "(" ++ Prelude.foldr (\(k, v) s -> show k ++ ", " ++ show v ++ "),\\allowbreak " ++ s) "" (Map.toList map) ++ ")"

showSet :: Show a => Set a -> String
showSet set = "{" ++ Prelude.foldr (\el s -> show el ++ ",\\allowbreak " ++ s) "" (Set.toList set) ++ "}"
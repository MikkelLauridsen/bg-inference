import Constraints
import Data.Map as Map
import qualified Data.Set as Set
import Engine (inferBound)
import Index
import IndexConstraintSolving
import Inference
import PiCalculus
import Test.Hspec
import TypeInference
import Types

inferenceSpec = describe "Inference" $ do
  it "should infer simple types of running example" $ do
    inferSimpleTypes 1 inferenceRunningExample
      `shouldBe` Right
        ( Map.fromList
            [ (b1, STServ (Set.singleton (IndexVar 0)) [STNat, STChannel []]),
              (b2, STChannel []),
              (b3, STChannel []),
              (b4, STChannel []),
              (b5, STNat),
              (b6, STChannel []),
              (b7, STNat)
            ]
        )

  it "should infer constraints for the running example" $ do
    inferTypes (Set.empty, Set.empty) Map.empty inferenceRunningExampleWithST
      `shouldSatisfy` \r ->
        case r of
          Right (a, _, _) | a == Map.empty -> True
          _ -> False

  it "should infer bound on simple example" $ do
    inferBound 1 (Set.empty, Set.empty) Map.empty simpleInfExample
      `shouldReturn` Right (Index (Map.empty, COENumeral 4))

  it "should infer bound on fib(3)" $ do
    inferBound 2 (Set.empty, Set.empty) Map.empty fib3
      `shouldReturn` Right (Index (Map.empty, COENumeral 3))

  it "should infer bound on running example" $ do
    inferBound 1 (Set.empty, Set.empty) Map.empty inferenceRunningExample
      `shouldReturn` Right (Index (Map.empty, COENumeral 1))

  it "should check index constraint 2 = 2" $ do
    solveIndexConstraints [ICSEqual (Index (Map.empty, COENumeral 2)) (Index (Map.empty, COENumeral 2))] `shouldReturn` Right Map.empty
  it "should check index constraint x = 2" $ do
    solveIndexConstraints [ICSEqual (Index (Map.empty, COEVar (CoeffVar 0))) (Index (Map.empty, COENumeral 2))] `shouldReturn` Right (Map.fromList [(CoeffVar 0, 2)])

main :: IO ()
main = do
  hspec inferenceSpec

typeVars :: [TypeVar]
typeVars = [0 ..]

simpleTypeVars :: [SimpleType]
simpleTypeVars = [STVar i | i <- typeVars]

b1 : b2 : b3 : b4 : b5 : b6 : b7 : br = typeVars

tb1 : tb2 : tb3 : tb4 : tb5 : tbr = simpleTypeVars

simpleInfExample :: Proc
simpleInfExample =
  TickP (TickP (TickP (TickP NilP)))

inferenceRunningExample :: Proc
inferenceRunningExample =
  RestrictP "npar" tb1 $
    RepInputP
      "npar"
      ["n", "r"]
      ( MatchNatP
          (VarE "n")
          (OutputP "r" [])
          "x"
          $ RestrictP "r'" tb2 $
            RestrictP
              "r''"
              tb3
              (  (TickP (OutputP "r'" []))
                  :|: OutputP "npar" [VarE "x", VarE "r''"]
                  :|: InputP "r'" [] (InputP "r''" [] $ OutputP "r" [])
              )
      )
      :|: RestrictP "r" tb4 (OutputP "npar" [natExp 10, VarE "r"] :|: InputP "r" [] NilP)

inferenceRunningExampleWithST :: Proc
inferenceRunningExampleWithST =
  RestrictP "npar" (STServ (Set.singleton (IndexVar 0)) [STNat, STChannel []]) $
    RepInputP
      "npar"
      ["n", "r"]
      ( MatchNatP
          (VarE "n")
          (OutputP "r" [])
          "x"
          $ RestrictP "r'" (STChannel []) $
            RestrictP
              "r''"
              (STChannel [])
              ( TickP (OutputP "r'" [])
                  :|: OutputP "npar" [VarE "x", VarE "r''"]
                  :|: InputP "r'" [] (InputP "r''" [] $ OutputP "r" [])
              )
      )
      :|: RestrictP "r" (STChannel []) (OutputP "npar" [natExp 2, VarE "r"] :|: InputP "r" [] NilP)



fib3 :: Proc
fib3 =
  RestrictP "add" tb1 $ RestrictP "fib" tb2 $ addProc :|: fibProc :|: RestrictP "rret" tb5 (OutputP "fib" [SuccE (SuccE (SuccE ZeroE)), VarE "rret"])


addProc :: Proc
addProc =
  RepInputP
    "add"
    ["n", "m", "r"]
    (MatchNatP
      (VarE "n")
      (OutputP "r" [VarE "m"])
      "n'"
      (OutputP "add" [VarE "n'", SuccE (VarE "m"), VarE "r"]))


fibProc :: Proc
fibProc =
  RepInputP 
    "fib" 
    ["x", "r"]
    (MatchNatP 
      (VarE "x")
      (OutputP "r" [ZeroE])
      "y"
      (MatchNatP
        (VarE "y")
        (OutputP "r" [SuccE ZeroE])
        "z"
        (RestrictP "r'" tb3 $ RestrictP "r''" tb4 (OutputP "r'" [(VarE "y")] :|: OutputP "r''" [VarE "z"] :|: InputP "r'" ["n"] (InputP "r''" ["m"] (TickP $ OutputP "add" [VarE "n", VarE "m", VarE "r"]))))
        ))


inferenceRunningExampleSim :: Proc
inferenceRunningExampleSim =
  RestrictP "npar" tb1 $
    RepInputP
      "npar"
      ["n", "r"]
      ( MatchNatP
          (VarE "n")
          (OutputP "r" [])
          "x"
          $ RestrictP "r'" tb2 
              (  TickP NilP
                  :|: OutputP "npar" [VarE "x", VarE "r'"]
                  :|: InputP "r'" [] (OutputP "r" [])
              )
      )
      :|: RestrictP "r" tb3 (OutputP "npar" [natExp 10, VarE "r"] :|: InputP "r" [] NilP)
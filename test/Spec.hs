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
  it "should substitute indices for index variables" $ do
    indexSubst (Index (Map.singleton (IndexVar 0) (COENumeral 2), COENumeral 1)) (Map.singleton (IndexVar 0) (Index (Map.empty, COENumeral 3)))
      `shouldBe` (Index (Map.empty, COEAdd (COEMul (COENumeral 2) (COENumeral 3)) (COENumeral 1)))

  it "should substitute indices for index variables (2)" $ do
    indexSubst (Index (Map.singleton (IndexVar 0) (COENumeral 2), COENumeral 1)) (Map.singleton (IndexVar 0) (Index (Map.singleton (IndexVar 0) (COENumeral 4), COENumeral 3)))
      `shouldBe` (Index (Map.singleton (IndexVar 0) (COEMul (COENumeral 2) (COENumeral 4)), COEAdd (COEMul (COENumeral 2) (COENumeral 3)) (COENumeral 1)))

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

  it "should infer simple types of fib(3)" $ do
    inferSimpleTypes 2 fib3
      `shouldBe` Right
        ( Map.fromList
            [ (0, STServ (Set.fromList [i1, i2]) [STNat, STNat, STChannel [STNat]]),
              (1, STServ (Set.fromList [i2, i3]) [STNat, STChannel [STNat]]),
              (2, STChannel [STNat]),
              (3, STChannel [STNat]),
              (4, STChannel [STNat]),
              (5, STNat),
              (6, STNat),
              (7, STChannel [STNat]),
              (8, STNat),
              (9, STNat),
              (10, STChannel [STNat]),
              (11, STNat),
              (12, STNat),
              (13, STNat),
              (14, STNat)
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

  it "should infer bound on simple parallel composition" $ do
    inferBound 1 (Set.empty, Set.empty) Map.empty simpleNilTestProc
      `shouldReturn` Right (Index (Map.empty, COENumeral 1))

  it "should infer bound on simple pattern match" $ do
    inferBound 1 (Set.empty, Set.empty) Map.empty simpleNilTestProc'
      `shouldReturn` Right (Index (Map.empty, COENumeral 1))

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
simpleTypeVars = Prelude.map STVar [0 ..]

indexVars :: [IndexVar]
indexVars = Prelude.map IndexVar [0 ..]

b1 : b2 : b3 : b4 : b5 : b6 : b7 : _ = typeVars

tb1 : tb2 : tb3 : tb4 : tb5 : _ = simpleTypeVars

i1 : i2 : i3 : _ = indexVars

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
              ( TickP (OutputP "r'" [])
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
  RestrictP "add" tb1 $ RestrictP "fib" tb2 $ addProc :|: fibProc :|: RestrictP "rret" tb5 (OutputP "fib" [natExp 3, VarE "rret"])

addProc :: Proc
addProc =
  RepInputP
    "add"
    ["n", "m", "r"]
    ( MatchNatP
        (VarE "n")
        (OutputP "r" [VarE "m"])
        "n'"
        (OutputP "add" [VarE "n'", SuccE (VarE "m"), VarE "r"])
    )

fibProc :: Proc
fibProc =
  RepInputP
    "fib"
    ["x", "r"]
    ( MatchNatP
        (VarE "x")
        (OutputP "r" [ZeroE])
        "y"
        ( MatchNatP
            (VarE "y")
            (OutputP "r" [SuccE ZeroE])
            "z"
            (RestrictP "r'" tb3 $ RestrictP "r''" tb4 (OutputP "r'" [VarE "y"] :|: OutputP "r''" [VarE "z"] :|: InputP "r'" ["n"] (InputP "r''" ["m"] (TickP $ OutputP "add" [VarE "n", VarE "m", VarE "r"]))))
        )
    )


simpleNilTestProc :: Proc
simpleNilTestProc =
  NilP :|: TickP NilP

simpleNilTestProc' :: Proc
simpleNilTestProc' =
  MatchNatP (SuccE ZeroE) NilP "n'" $ TickP NilP
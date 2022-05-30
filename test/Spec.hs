import Constraints
import Data.Map as Map
import Index
import IndexConstraintSolving
import Inference
import PiCalculus
import Test.Hspec
import Types
import qualified Data.Set as Set

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
  it "should check index constraint 2 = 2" $ do
    solveIndexConstraints [ICSEqual (Map.empty, COENumeral 2) (Map.empty, COENumeral 2)] `shouldReturn` Right Map.empty
  it "should check index constraint x = 2" $ do
    solveIndexConstraints [ICSEqual (Map.empty, COEVar (CoeffVar 0)) (Map.empty, COENumeral 2)] `shouldReturn` Right (Map.fromList [(CoeffVar 0, 2)])

main :: IO ()
main = do
  hspec inferenceSpec

typeVars :: [TypeVar]
typeVars = [0 ..]

simpleTypeVars :: [SimpleType]
simpleTypeVars = [STVar i | i <- typeVars]

b1 : b2 : b3 : b4 : b5 : b6 : b7 : br = typeVars

tb1 : tb2 : tb3 : tb4 : tbr = simpleTypeVars

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
      :|: RestrictP "r" tb4 (OutputP "npar" [natExp 2, VarE "r"] :|: InputP "r" [] NilP)
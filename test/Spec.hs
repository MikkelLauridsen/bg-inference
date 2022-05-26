import Data.Map as Map
import Inference
import PiCalculus
import Test.Hspec
import Types

inferenceSpec = describe "Inference" $ do
  it "should infer simple types of running example" $ do
    inferSimpleTypes 1 inferenceRunningExample
      `shouldBe` ( Right $
                     Map.fromList
                       [ (b1, STServ [0] [STNat, STChannel []]),
                         (b2, STChannel []),
                         (b3, STChannel []),
                         (b4, STChannel []),
                         (b5, STNat),
                         (b6, STChannel []),
                         (b7, STNat)
                       ]
                 )

main :: IO ()
main = hspec inferenceSpec

typeVars :: [TypeVar]
typeVars = [0 ..]

simpleTypeVars :: [SimpleType]
simpleTypeVars = [STVar i | i <- typeVars]

b1 : b2 : b3 : b4 : b5 : b6 : b7 : br = typeVars

tb1 : tb2 : tb3 : tb4 : tbr = simpleTypeVars

inferenceRunningExample :: Proc
inferenceRunningExample =
  RestrictP "npar" tb1 $
    ( RepInputP "npar" ["n", "r"] $
        MatchNatP
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
      :|: (RestrictP "r" tb4 (OutputP "npar" [natExp 2, VarE "r"] :|: InputP "r" [] NilP))
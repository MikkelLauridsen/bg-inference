module Main where


import PiCalculus
import Engine
import Types
import Index
import Constraints
import Data.Set as Set
import Data.Map as Map


main :: IO ()
main = inferBoundVerbose 1 (Set.empty, Set.empty) (Map.singleton "add" $ STServ (Set.fromList [IndexVar 0, IndexVar 1]) [STNat, STNat, STChannel [STNat]]) addtest >>= print
--main = inferBoundVerbose 1 (Set.empty, Set.empty) (Map.singleton "npar" $ STServ (Set.fromList [IndexVar 0]) [STNat, STChannel []]) inferenceRunningExamplef' >>= print
--main = inferBoundVerbose 1 (Set.empty, Set.empty) (Map.singleton "seq" $ STServ (Set.fromList [IndexVar 0]) [STNat]) exmptest' >>= print


typeVars :: [TypeVar]
typeVars = [0 ..]

simpleTypeVars :: [SimpleType]
simpleTypeVars = [STVar i | i <- typeVars]

tb1 : tb2 : tb3 : tb4 : tb5 : tbr = simpleTypeVars

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
          $ RestrictP "r'" tb2
              (  (TickP NilP)
                  :|: OutputP "npar" [VarE "x", VarE "r'"]
                  :|: InputP "r'" [] (OutputP "r" [])
              )
      )
      :|: RestrictP "r" tb4 (OutputP "npar" [natExp 2, VarE "r"] :|: InputP "r" [] NilP)

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
              (TickP $ TickP (OutputP "npar" [VarE "x", VarE "r'"]
                  :|: InputP "r'" [] (OutputP "r" [])
              ))
      )
      :|: RestrictP "r" tb3 (OutputP "npar" [natExp 10, VarE "r"] :|: InputP "r" [] NilP)


exmptest :: Proc
exmptest =
    RestrictP "seq" tb1 $
        RepInputP "seq" ["n"] $
            MatchNatP (VarE "n") NilP "n'" $
                TickP (OutputP "seq" [VarE "n'"])


exmptest' :: Proc
exmptest' =
    (RepInputP "seq" ["n"] $
        MatchNatP (VarE "n") NilP "n'" $
            TickP (OutputP "seq" [VarE "n'"]))
            :|: (OutputP "seq" [natExp 10])



addtest :: Proc
addtest =
    RepInputP "add" ["x", "y", "r"] $
        MatchNatP (VarE "x") (OutputP "r" [VarE "y"]) "z" $
            OutputP "add" [VarE "z", SuccE (VarE "y"), VarE "r"]



inferenceRunningExample2 :: Proc
inferenceRunningExample2 =
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
              (TickP (OutputP "r'" []
                  :|: OutputP "npar" [VarE "x", VarE "r''"]
                  :|: InputP "r'" [] (InputP "r''" [] $ OutputP "r" []))
              )
      )
      :|: RestrictP "r" tb4 (OutputP "npar" [natExp 10, VarE "r"] :|: InputP "r" [] NilP)
                


inferenceRunningExample2' :: Proc
inferenceRunningExample2' =
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
              (TickP (OutputP "r'" []
                  :|: OutputP "npar" [VarE "x", VarE "r''"]
                  :|: InputP "r'" [] (InputP "r''" [] $ OutputP "r" []))
              )
      )
                

inferenceRunningExample2'' :: Proc
inferenceRunningExample2'' =
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
              (TickP (OutputP "r'" []
                  :|: OutputP "npar" [VarE "x", VarE "r''"]
                  :|: InputP "r'" [] (InputP "r''" [] $ OutputP "r" []))
              )
      )


inferenceRunningExamplef :: Proc
inferenceRunningExamplef =
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


inferenceRunningExamplef' :: Proc
inferenceRunningExamplef' =
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
              (TickP ((OutputP "r'" [])
                  :|: OutputP "npar" [VarE "x", VarE "r''"]
                  :|: InputP "r'" [] (InputP "r''" [] $ OutputP "r" [])
              ))
      )
      :|: RestrictP "r" tb4 (OutputP "npar" [natExp 10, VarE "r"] :|: InputP "r" [] NilP)
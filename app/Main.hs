module Main where


import PiCalculus
import Engine
import Types
import Index
import Constraints
import Data.Set as Set
import Data.Map as Map


main :: IO ()
main = inferBoundVerbose 1 (Set.empty, Set.empty) Map.empty inferenceRunningExample >>= print


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
          $ RestrictP "r'" tb2 $
            RestrictP
              "r''"
              tb3
              (  (TickP (OutputP "r'" []))
                  :|: OutputP "npar" [VarE "x", VarE "r''"]
                  :|: InputP "r'" [] (InputP "r''" [] $ OutputP "r" [])
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
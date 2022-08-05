module Main where


import PiCalculus
import Engine
import Types
import Index
import Constraints
import Data.Set as Set
import Data.Map as Map
import Parser (parse, addFreshTypeVars)
import Lexer (tokenize)
import System.Environment
import System.IO


main :: IO ()
main = do
  args <- getArgs
  case args of
    [filePath] -> do
      s <- readFile filePath
      case tokenize s of
        Nothing -> putStrLn "lexing error"
        Just tokens ->
          case parse tokens of
            Nothing -> putStrLn "parse error"
            Just process -> do
              let process' = addFreshTypeVars process
              print process'
              inferBound 1 (Set.empty, Set.empty) Map.empty process' >>= print
    _ -> putStrLn "invalid invocation; must be called with a filepath"

--main = inferBoundVerbose 1 (Set.empty, Set.empty) (Map.singleton "add" $ STServ (Set.fromList [IndexVar 0, IndexVar 1]) [STNat, STNat, STChannel [STNat]]) addtest >>= print
--main = inferBoundVerbose 1 (Set.empty, Set.empty) (Map.singleton "npar" $ STServ (Set.fromList [IndexVar 0]) [STNat, STChannel []]) inferenceRunningExample2' >>= print
--main = inferBoundVerbose 1 (Set.empty, Set.empty) (Map.singleton "seq" $ STServ (Set.fromList [IndexVar 0]) [STNat]) exmptest' >>= print
--main = do
--  putStrLn ""
--  putStrLn "Process: tick.tick.tick.tick.0"
--  simpleInfRes <- inferBound 1 (Set.empty, Set.empty) Map.empty simpleInfExample
--  putStrLn $ "Inferred bound: " ++ show simpleInfRes
--  putStrLn ""
--  putStrLn ""
--  putStrLn "Process: !npar(n,r).match n { 0 -> r<>; s(x) -> (vr')(tick.0 | npar<x,r'> | r'().r<>) } | (nr)(npar<10,r> | r().0)"
--  runningExmpRes <- inferBound 1 (Set.empty, Set.empty) Map.empty inferenceRunningExample
--  putStrLn $ "Inferred bound: " ++ show runningExmpRes
--  putStrLn ""
--  putStrLn ""
--  putStrLn "Process: !seq(n,r).match n { 0 -> r<>; s(x) -> (vr')(tick.seq<x,r'> | r'().r<>) } | (nr)(seq<10,r> | r().0)"
--  runningExmpRes2 <- inferBound 1 (Set.empty, Set.empty) Map.empty inferenceRunningExampleSim
--  putStrLn $ "Inferred bound: " ++ show runningExmpRes2




typeVars :: [TypeVar]
typeVars = [0 ..]

simpleTypeVars :: [SimpleType]
simpleTypeVars = [STVar i | i <- typeVars]

tb1 : tb2 : tb3 : tb4 : tb5 : tbr = simpleTypeVars

simpleInfExample =
  TickP (TickP (TickP (TickP NilP)))

-- !npar(n,r).match n { 0 -> r<>; s(x) -> (vr')(tick.0 | npar<x,r'> | r'().r<>) } | (nr)(npar<10,r> | r().0)
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
      :|: RestrictP "r" tb4 (OutputP "npar" [natExp 10, VarE "r"] :|: InputP "r" [] NilP)

-- !seq(n,r).match n { 0 -> r<>; s(x) -> (vr')(tick.seq<x,r'> | r'().r<>) } | (nr)(seq<10,r> | r().0)
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
              (TickP (OutputP "npar" [VarE "x", VarE "r'"]
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
    RepInputP "seq" ["n"] (
        MatchNatP (VarE "n") NilP "n'" $
            TickP (OutputP "seq" [VarE "n'"]))
            :|: OutputP "seq" [natExp 10]



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

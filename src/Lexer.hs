module Lexer (
  tokenize
) where

import Data.Char

data Token 
    = NewT
    | InT
    | VarT String
    | RepT
    | DotT
    | QuestionT
    | ExclamationT
    | ParenLT
    | ParenRT
    | SepaT
    | CommaT
    | NatT Int
    | TickT
    | MatchT
    | CurlyLT
    | CurlyRT
    | SemiT
    | ArrowT

tokenize :: String -> Maybe [Token]
tokenize = aux False
    where
        aux _ "" = Just []       
        aux True ('*':'*':'*':'/':s) = aux False s
        aux True (c:s) = aux True s
        aux False (c:s) | isSpace c = aux False s 
        aux False ('/':'*':'*':'*':s) = aux True s
        aux False ('n':'e':'w':s) = aux False s >>= (\tokens -> return $ NewT : tokens)
        aux False ('i':'n':s) = aux False s >>= (\tokens -> return $ InT : tokens)
        aux False ('*':s) = aux False s >>= (\tokens -> return $ RepT : tokens)
        aux False ('.':s) = aux False s >>= (\tokens -> return $ DotT : tokens)
        aux False ('?':s) = aux False s >>= (\tokens -> return $ QuestionT : tokens)
        aux False ('!':s) = aux False s >>= (\tokens -> return $ ExclamationT : tokens)
        aux False ('(':s) = aux False s >>= (\tokens -> return $ ParenLT : tokens)
        aux False (')':s) = aux False s >>= (\tokens -> return $ ParenRT : tokens)
        aux False ('|':s) = aux False s >>= (\tokens -> return $ SepaT : tokens)
        aux False (',':s) = aux False s >>= (\tokens -> return $ CommaT : tokens)
        aux False ('t':'i':'c':'k':s) = aux False s >>= (\tokens -> return $ TickT : tokens)
        aux False ('m':'a':'t':'c':'h':s) = aux False s >>= (\tokens -> return $ MatchT : tokens)
        aux False ('{':s) = aux False s >>= (\tokens -> return $ CurlyLT : tokens)
        aux False ('}':s) = aux False s >>= (\tokens -> return $ CurlyRT : tokens)
        aux False (';':s) = aux False s >>= (\tokens -> return $ SemiT : tokens)
        aux False ('-':'>':s) = aux False s >>= (\tokens -> return $ ArrowT : tokens)
        aux False s@(c:_) | isDigit c = aux False (dropWhile isSpace s) >>= (\tokens -> return $ (NatT $ (read :: String -> Int) (takeWhile isSpace s)) : tokens)
        aux False s@(c:_) | isLetter c = do
            let prefix = takeWhile isLetter s
            let s' = dropWhile isLetter s
            let postfix = takeWhile isDigit $ s'
            tokens <- aux False $ dropWhile isDigit s'
            return $ VarT (prefix ++ postfix) : tokens
        aux _ _ = Nothing



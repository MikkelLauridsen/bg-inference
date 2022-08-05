module Lexer (
  tokenize
,  Token (..)
) where

import Data.Char

data Token 
    = NewT         -- new
    | SuccT        -- succ
    | ZeroT        -- zero
    | NilT         -- nil
    | InT          -- in
    | VarT String  -- [a-z]+[0-9]*
    | RepT         -- *
    | DotT         -- .
    | QuestionT    -- ?
    | ExclamationT -- !
    | ParenLT      -- (
    | ParenRT      -- )
    | SepaT        -- |
    | CommaT       -- ,
    | NatT Int     -- [0-9]+
    | TickT        -- tick
    | MatchT       -- match
    | CurlyLT      -- {
    | CurlyRT      -- }
    | SemiT        -- ;
    | ArrowT       -- ->
    deriving Eq

tokenize :: String -> Maybe [Token]
tokenize = aux False
    where
        aux _ "" = Just []       
        aux True ('*':'*':'*':'/':s) = aux False s
        aux True (c:s) = aux True s
        aux False (c:s) | isSpace c = aux False s 
        aux False ('/':'*':'*':'*':s) = aux True s
        aux False ('n':'e':'w':s) = aux False s >>= (\tokens -> return $ NewT : tokens)
        aux False ('s':'u':'c':'c':s) = aux False s >>= (\tokens -> return $ SuccT : tokens)
        aux False ('z':'e':'r':'o':s) = aux False s >>= (\tokens -> return $ ZeroT : tokens)
        aux False ('n':'i':'l':s) = aux False s >>= (\tokens -> return $ NilT : tokens)
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
        aux False s@(c:_) | isDigit c = aux False (dropWhile isDigit s) >>= (\tokens -> return $ (NatT $ (read :: String -> Int) (takeWhile isDigit s)) : tokens)
        aux False s@(c:_) | isLetter c = do
            let prefix = takeWhile isLetter s
            let s' = dropWhile isLetter s
            let postfix = takeWhile isDigit $ s'
            tokens <- aux False $ dropWhile isDigit s'
            return $ VarT (prefix ++ postfix) : tokens
        aux _ _ = Nothing



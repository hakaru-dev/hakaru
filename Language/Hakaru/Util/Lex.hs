-- TODO: [wrengr 2015.10.23] (a) remove this file entirely, or (b) move it somewhere more helpful. Probably the latter.

{-# OPTIONS -W #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Text.Read.Lex
-- Copyright   :  (c) The University of Glasgow 2002
-- License     :  BSD-style (see the file libraries/base/LICENSE)
--
-- Maintainer  :  libraries@haskell.org
-- Stability   :  provisional
-- Portability :  non-portable (uses Text.ParserCombinators.ReadP)
--
-- The cut-down Haskell lexer, used by Text.Read
--
-----------------------------------------------------------------------------

module Language.Hakaru.Util.Lex (readMapleString, lexMapleString) where

import Text.ParserCombinators.ReadP
import Data.Char
import Control.Monad

readMapleString :: String -> Maybe String
readMapleString s =
  case [ x | (x,"") <- readP_to_S p s ] of
    [x] -> Just x
    _ -> Nothing
  where p = do x <- lexMapleString
               skipSpaces
               return x

lexMapleString :: ReadP String
lexMapleString = fmap concat (many1 (skipSpaces >> lexString))

lexCharE :: ReadP (Char, Bool)  -- "escaped or not"?
lexCharE =
  do c1 <- get
     if c1 == '\\'
       then do c2 <- lexEsc; return (c2, True)
       else do return (c1, False)
 where
  lexEsc =
    lexEscChar
      +++ lexNumeric

  lexEscChar =
    do c <- get
       case c of
         'a'  -> return '\a'
         'b'  -> return '\b'
         'e'  -> return '\27' -- Maple is different from Haskell here
         'f'  -> return '\f'
         'n'  -> return '\n'
         'r'  -> return '\r'
         't'  -> return '\t'
         'v'  -> return '\v'
         '\\' -> return '\\'
         '\"' -> return '\"'
         '\'' -> return '\''
         _    -> pfail

  lexNumeric =
    do _    <- char 'x'
       n    <- lexInteger16
       guard (n <= toInteger (ord maxBound))
       return (chr (fromInteger n))

-- ---------------------------------------------------------------------------
-- string literal

lexString :: ReadP String
lexString =
  do _ <- char '"'
     body id
 where
  body f =
    do (c,esc) <- lexStrItem
       if c /= '"' || esc
         then body (f.(c:))
         else (char '"' >> body (f.(c:))) +++ return (f "")

  lexStrItem = (lexEmpty >> lexStrItem)
               +++ lexCharE

  lexEmpty = -- Maple is different from Haskell here
    do _ <- char '\\'
       satisfy isSpace

-- ---------------------------------------------------------------------------
--  Lexing numbers

type Digits = [Int]

lexDigits16 :: ReadP Digits
-- Lex a non-empty sequence of hexadecimal digits
lexDigits16 =
  do s  <- look
     xs <- scan s id
     guard (not (null xs))
     return xs
 where
  scan (c:cs) f = case valDig16 c of
                    Just n  -> do _ <- get; scan cs (f.(n:))
                    Nothing -> do return (f [])
  scan []     f = do return (f [])

lexInteger16 :: ReadP Integer
lexInteger16 =
  do xs <- lexDigits16
     return (val 16 0 xs)

val :: Num a => a -> a -> Digits -> a
-- val base y [d1,..,dn] = y ++ [d1,..,dn], as it were
val _    y []     = y
val base y (x:xs) = y' `seq` val base y' xs
 where
  y' = y * base + fromIntegral x

valDig16 :: Char -> Maybe Int
valDig16 c
  | '0' <= c && c <= '9' = Just (ord c - ord '0')
  | 'a' <= c && c <= 'f' = Just (ord c - ord 'a' + 10)
  | 'A' <= c && c <= 'F' = Just (ord c - ord 'A' + 10)
  | otherwise            = Nothing


{-# LANGUAGE NoMonomorphismRestriction, FlexibleContexts #-}
module Text.Parsec.Indentation.Examples.Parens where

-- Encodes example TODO from the paper TODO.
-- Note that because Parsec doesn't support full backtracking
-- this

import Control.Applicative
import Text.Parsec
import Text.Parsec.Indentation

data A
  = Par A   -- '(' A ')'
  | Bra A   -- '[' A ']'
  | Seq A A -- A A
  | Nil     -- epsilon
  deriving (Show, Eq)

a :: (Monad m, Stream s m (Char, Indentation)) => ParsecT (IndentStream s) () m A
a = choice [ Seq <$> a' <*> a, a', return Nil ]

a' :: (Monad m, Stream s m (Char, Indentation)) => ParsecT (IndentStream s) () m A
a' = choice
    [ Par <$>
        between (localTokenMode (const Eq) $ char '(')
                (localTokenMode (const Eq) $ char ')')
                (localIndentation Gt a)
    , Bra <$>
        between (localTokenMode (const Ge) $ char '[')
                (localTokenMode (const Ge) $ char ']')
                (localIndentation Gt a)
    ]


runParse input
  = case runParser a () "" (mkIndentStream 0 infIndentation True Gt input) of
      Left err -> Left (show err)
      Right a  -> Right a

input1 = [('(', 1),
          ('[', 4),
          ('(', 5),
          (')', 5),
          (']', 7),
          (')', 1)]
output1 = runParse input1

input2 = [('(', 1),
          ('[', 8),
          ('(', 6),
          (')', 6),
          ('[', 8),
          (']', 9),
          (']', 4),
          ('(', 3),
          (')', 3),
          (')', 1)]
output2 = runParse input2

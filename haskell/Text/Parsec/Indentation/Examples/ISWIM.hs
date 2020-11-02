module Text.Parsec.Indentation.Examples.ISWIM where

-- Encodes example TODO from the paper TODO.
-- Note that because Parsec doesn't support full backtracking
-- this
--

import Control.Applicative ((<$>))
import Text.Parsec
import Text.Parsec.Indentation
import Text.Parsec.Indentation.Char

data ID = ID String deriving (Show, Eq)
data Expr
  = Where Expr ID Expr -- expr -> expr 'where' ID '=' |expr|>=
  | Plus Expr Expr     -- expr -> expr '+' expr
  | Minus Expr         -- expr -> '-' expr
  | Parens Expr        -- expr -> '(' expr* ')'
  | Var ID             -- expr -> ID
  deriving (Show, Eq)

runParse :: String -> Either ParseError Expr
runParse input
  = case runParser expr () "" (mkIndentStream 0 infIndentation True Ge (mkCharIndentStream input)) of
      Left err -> Left err
      Right a  -> Right a

-- Note that this grammar DOES NOT WORK as written because it contains
-- a left recursion.  (It diverges.)  However, it provides a good
-- first example to see how to use the combinators in
-- Text.Parsec.Indentation.

tok s = string s >> localTokenMode (const Any) (ignoreAbsoluteIndentation (many (char ' ' <|> char '\n')))
ident = choice (map f ["v", "w", "x", "y", "z"])
  where f x = tok x >> return (ID x)

expr = choice $ map try
    [ do e1 <- expr_nonrec
         tok "where"
         i <- ident
         tok "="
         e2 <- localIndentation Ge (absoluteIndentation expr)
         return (Where e1 i e2)
    , do e1 <- expr_nonrec
         tok "+"
         e2 <- expr
         return (Plus e1 e2)
    , expr_nonrec
    ]

expr_nonrec = choice
    [ tok "-" >> (Minus <$> expr)
    , Parens <$> between (tok "(") (tok ")") (localIndentation Any expr)
    , Var <$> ident
    ]


input1 = "x + v where\n\
         \ x = -(\n\
         \y + z) + w"
output1 = runParse input1

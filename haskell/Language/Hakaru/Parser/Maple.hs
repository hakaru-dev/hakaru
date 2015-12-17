{-# LANGUAGE CPP
           , RankNTypes
           , GADTs
           , ExistentialQuantification
           , StandaloneDeriving
           , OverloadedStrings
           #-}
{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
module Language.Hakaru.Parser.Maple where

import           Language.Hakaru.Parser.AST
import           Control.Monad.Identity
import           Data.Text           (Text)
import qualified Data.Text           as Text
#if __GLASGOW_HASKELL__ < 710
import           Data.Functor        ((<$>))
import           Control.Applicative (Applicative(..))
#endif
import           Text.Parsec
import           Text.Parsec.Text
import qualified Text.Parsec.Token   as Token
import           Text.Parsec.Language

style :: GenLanguageDef Text st Identity
style = Token.LanguageDef
    { Token.commentStart   = "(*"
    , Token.commentEnd     = "*)"
    , Token.commentLine    = "#"
    , Token.nestedComments = True
    , Token.identStart     = letter <|> char '_'
    , Token.identLetter    = alphaNum <|> oneOf "_"
    , Token.opStart        = Token.opLetter style
    , Token.opLetter       = oneOf "+-*/<>="
    , Token.reservedOpNames= []
    , Token.reservedNames  = []
    , Token.caseSensitive  = False
    }

symTable :: [(Text, Text)]
symTable =
    [ ("Gaussian", "normal")
    , ("BetaD",    "beta")
    , ("GammaD",   "gamma")
    , ("Weight",   "weight")
    , ("Uniform",  "uniform")
    , ("Ret",      "dirac")
    ]

type TokenParser a = Token.GenTokenParser Text a Identity

data NumOp = Pos | Neg deriving (Eq, Show)

data ArgOp
    = Float | Power | Rational
    | Func  | ExpSeq
    deriving (Eq, Show)

data InertExpr
    = InertName Text
    | InertNum  NumOp Integer
    | InertArgs ArgOp [InertExpr]
    deriving (Eq, Show)

lexer :: TokenParser ()
lexer = Token.makeTokenParser style

integer :: Parser Integer
integer = Token.integer lexer

parens :: Parser a -> Parser a
parens = Token.parens lexer

identifier :: Parser Text
identifier = Text.pack <$> Token.identifier lexer

stringLiteral :: Parser Text
stringLiteral = Text.pack <$> Token.stringLiteral lexer

commaSep :: Parser a -> Parser [a]
commaSep = Token.commaSep lexer

arg :: Parser a -> Parser [a]
arg e = parens (commaSep e)

apply1 :: Parser a -> Parser a
apply1 e = do
    args <- arg e
    case args of
        [e'] -> return e'
        _    -> error "Expected only one argument"

apply2 :: Parser a -> Parser (a, a)
apply2 e = do
    args <- arg e
    case args of
        [e1, e2] -> return (e1, e2)
        _        -> error "Expected only two arguments"

text :: Text -> Parser Text
text = liftM Text.pack <$> string <$> Text.unpack

expr :: Parser InertExpr
expr =  try func
    <|> try name
    <|> try assignedname
    <|> try expseq
    <|> try intpos
    <|> try intneg
    <|> try power
    <|> try rational
    <|> float

func :: Parser InertExpr
func = InertArgs <$> (text "_Inert_FUNCTION" *> return Func) <*> arg expr

name :: Parser InertExpr
name = InertName <$> (text "_Inert_NAME" *> apply1 stringLiteral)

assignedname :: Parser InertExpr
assignedname = InertName <$> (text "_Inert_ASSIGNEDNAME" *> (fst <$> apply2 stringLiteral))

expseq :: Parser InertExpr
expseq = InertArgs <$> (text "_Inert_EXPSEQ" *> return ExpSeq) <*> arg expr

intpos :: Parser InertExpr
intpos = InertNum <$> (text "_Inert_INTPOS" *> return Pos) <*> apply1 integer

intneg :: Parser InertExpr
intneg = InertNum <$> (text "_Inert_INTNEG" *> return Neg) <*> fmap negate (apply1 integer)

float :: Parser InertExpr
float  = InertArgs <$> (text "_Inert_FLOAT" *> return Float) <*> arg expr

power :: Parser InertExpr
power = InertArgs <$> (text "_Inert_POWER" *> return Power) <*> arg expr

rational :: Parser InertExpr
rational = InertArgs <$> (text "_Inert_RATIONAL" *> return Rational) <*> arg expr

rename :: Text -> Text
rename x =
    case lookup x symTable of
    Just x' -> x'
    Nothing -> x

parseMaple :: Text -> Either ParseError InertExpr
parseMaple = runParser (expr <* eof) () "<input>"

maple2AST :: InertExpr -> AST' Text
maple2AST (InertNum Pos i) = ULiteral $ Nat $ fromInteger i
maple2AST (InertNum Neg i) = ULiteral $ Int $ fromInteger i
maple2AST (InertName t)    = Var (rename t)

maple2AST (InertArgs Float [InertNum Pos a, InertNum p b]) = 
    ULiteral $ Prob $ fromInteger a * (10 ** (fromInteger b))

maple2AST (InertArgs Float [InertNum Neg a, InertNum p b]) = 
    ULiteral $ Real $ fromInteger a * (10 ** (fromInteger b))

maple2AST (InertArgs Func [f, (InertArgs ExpSeq a)]) =
    foldl App (maple2AST f) (map maple2AST a)
-- Add special case for NatPow for Power
maple2AST (InertArgs Power [x, y]) =
    App (App (Var "**") (maple2AST x)) (maple2AST y)
maple2AST (InertArgs Rational [InertNum _ x, InertNum _ y]) =
    ULiteral $ Real $ fromInteger x / fromInteger y
    

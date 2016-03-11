{-# LANGUAGE CPP, OverloadedStrings #-}
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

import           Prelude             hiding (sum, product)

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
    , ("True",     "true")
    , ("False",    "false")
    , ("Pi",       "pi")
    -- Type symbols
    , ("Real",     "real")
    , ("Prob",     "prob")
    , ("Measure",  "measure")
    , ("Bool",     "bool")
    ]

type TokenParser a = Token.GenTokenParser Text a Identity

data NumOp = Pos | Neg
    deriving (Eq, Show)

data ArgOp
    = Float   | Power  | Rational
    | Func    | ExpSeq | Sum_
    | Product
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
    <|> try sum
    <|> try product
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

sum :: Parser InertExpr
sum = InertArgs <$> (text "_Inert_SUM" *> return Sum_) <*> arg expr

product :: Parser InertExpr
product = InertArgs <$> (text "_Inert_PROD" *> return Product) <*> arg expr

rational :: Parser InertExpr
rational = InertArgs <$> (text "_Inert_RATIONAL" *> return Rational) <*> arg expr

rename :: Text -> Text
rename x =
    case lookup x symTable of
    Just x' -> x'
    Nothing -> x

parseMaple :: Text -> Either ParseError InertExpr
parseMaple txt = runParser (expr <* eof) () (Text.unpack txt) (Text.filter (/= '\n') txt)

maple2AST :: InertExpr -> AST' Text
maple2AST (InertNum Pos i) = ULiteral $ Nat $ fromInteger i
maple2AST (InertNum Neg i) = ULiteral $ Int $ fromInteger i

maple2AST (InertName t)    = Var (rename t)

maple2AST (InertArgs Float [InertNum Pos a, InertNum _ b]) = 
    ULiteral $ Prob $ fromInteger a * (10 ** (fromInteger b))

maple2AST (InertArgs Float [InertNum Neg a, InertNum _ b]) = 
    ULiteral $ Real $ fromInteger a * (10 ** (fromInteger b))

maple2AST (InertArgs Func [InertName "Ann", InertArgs ExpSeq [typ, e]]) =
    Ann (maple2AST e) (maple2Type typ)

maple2AST (InertArgs Func [InertName "Bind",
                           InertArgs ExpSeq [e1, InertName x, e2]]) =
    Bind x (maple2AST e1) (maple2AST e2)

maple2AST (InertArgs Func [InertName "Pair",
                           InertArgs ExpSeq [e1, e2]]) =
    Pair (maple2AST e1) (maple2AST e2)

maple2AST (InertArgs Func [InertName "Msum",
                           InertArgs ExpSeq es]) =
    Msum (map maple2AST es)

maple2AST (InertArgs Func [InertName "Case",
                           InertArgs ExpSeq
                           [e1, InertArgs Func [InertName "Branches",
                                                InertArgs ExpSeq bs]]]) =
    Case (maple2AST e1) (map branch bs)

maple2AST (InertArgs Func [f, (InertArgs ExpSeq a)]) =
    foldl App (maple2AST f) (map maple2AST a)

maple2AST (InertArgs Sum_ es) = NaryOp Sum (map maple2AST es)

maple2AST (InertArgs Product es) = NaryOp Prod (map maple2AST es)

-- Add special case for NatPow for Power
maple2AST (InertArgs Power [x, y]) =
    App (App (Var "**") (maple2AST x)) (maple2AST y)
maple2AST (InertArgs Rational [InertNum _ x, InertNum _ y]) =
    ULiteral $ Real $ fromInteger x / fromInteger y

maple2AST x = error $ "Can't handle: " ++ show x
    
maple2Type :: InertExpr -> TypeAST'
-- TODO: Add Arrow
maple2Type (InertName t) = TypeVar (rename t)
maple2Type (InertArgs Func [InertName f, InertArgs ExpSeq args]) =
    TypeApp (rename f) (map maple2Type args)


branch :: InertExpr -> Branch' Text
branch (InertArgs Func
        [InertName "Branch",
         InertArgs ExpSeq [pat, e]]) =
 Branch' (maple2Pattern pat) (maple2AST e)


maple2Pattern :: InertExpr -> Pattern' Text
maple2Pattern (InertName "PWild") = PWild'
maple2Pattern (InertArgs Func
               [InertName "PVar",
                InertArgs ExpSeq
                [InertName x]]) = PVar' x
maple2Pattern (InertArgs Func
               [InertName "PDatum",
                InertArgs ExpSeq
                [InertName "pair", args]]) =
  PPair' (map maple2Pattern (unpairPat args))
maple2Pattern e = error ("TODO: maple2AST{pattern} " ++ show e)

unpairPat :: InertExpr -> [InertExpr]
unpairPat (InertArgs Func [InertName "PInl",
 InertArgs ExpSeq
 [InertArgs Func
  [InertName "PEt",
   InertArgs ExpSeq
   [InertArgs Func
    [InertName "PKonst",
     InertArgs ExpSeq [x]],
    InertArgs Func
    [InertName "PEt",
     InertArgs ExpSeq
     [InertArgs Func
      [InertName "PKonst",
       InertArgs ExpSeq [y]],
      InertName "PDone"]]]]]]) = [x,y]
unpairPat _ = error "unpairPat: not InertExpr of a pair pattern"

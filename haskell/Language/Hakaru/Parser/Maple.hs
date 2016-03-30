{-# LANGUAGE CPP, OverloadedStrings #-}
{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
module Language.Hakaru.Parser.Maple where

import           Language.Hakaru.Parser.AST hiding (Less, Equal)
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
    , ("Lebesgue", "lebesgue")
    , ("Uniform",  "uniform")
    , ("Ret",      "dirac")
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
    | Product | Less   | Equal
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

comma :: Parser String
comma = Token.comma lexer

commaSep :: Parser a -> Parser [a]
commaSep = Token.commaSep lexer

arg :: Parser a -> Parser [a]
arg e = parens (commaSep e)

text :: Text -> Parser Text
text = liftM Text.pack <$> string <$> Text.unpack

expr :: Parser InertExpr
expr =  try func
    <|> try name
    <|> try assignedname
    <|> try assignedlocalname
    <|> try lessthan
    <|> try equal
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
name = InertName <$> (text "_Inert_NAME" *> parens stringLiteral)

assignedname :: Parser InertExpr
assignedname = InertName <$> (text "_Inert_ASSIGNEDNAME" *> parens (stringLiteral <* comma <* stringLiteral))

assignedlocalname :: Parser InertExpr
assignedlocalname = InertName <$> (text "_Inert_ASSIGNEDLOCALNAME" *> parens (stringLiteral <* comma <* stringLiteral <* comma <* integer))

expseq :: Parser InertExpr
expseq = InertArgs <$> (text "_Inert_EXPSEQ" *> return ExpSeq) <*> arg expr

intpos :: Parser InertExpr
intpos = InertNum <$> (text "_Inert_INTPOS" *> return Pos) <*> parens integer

intneg :: Parser InertExpr
intneg = InertNum <$> (text "_Inert_INTNEG" *> return Neg) <*> fmap negate (parens integer)

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

lessthan :: Parser InertExpr
lessthan = InertArgs <$> (text "_Inert_LESSTHAN" *> return Less) <*> arg expr

equal :: Parser InertExpr
equal = InertArgs <$> (text "_Inert_EQUATION" *> return Equal) <*> arg expr

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

maple2AST (InertName "infinity") = Infinity'
maple2AST (InertName t)    = Var (rename t)

maple2AST (InertArgs Float [InertNum Pos a, InertNum _ b]) = 
    ULiteral $ Prob $ fromInteger a * (10 ** (fromInteger b))

maple2AST (InertArgs Float [InertNum Neg a, InertNum _ b]) = 
    ULiteral $ Real $ fromInteger a * (10 ** (fromInteger b))

maple2AST (InertArgs Func [InertName "Bind",
                           InertArgs ExpSeq [e1, InertName x, e2]]) =
    Bind x (maple2AST e1) (maple2AST e2)

maple2AST (InertArgs Func [InertName "Datum",
                           InertArgs ExpSeq [InertName h, d]]) =
    mapleDatum2AST h d


maple2AST (InertArgs Func [InertName "lam",
                           InertArgs ExpSeq [InertName x, typ, e1]]) =
    Lam x (maple2Type typ) (maple2AST e1)

maple2AST (InertArgs Func [InertName "Msum",
                           InertArgs ExpSeq es]) =
    Msum (map maple2AST es)

maple2AST (InertArgs Func [InertName "case",
                           InertArgs ExpSeq
                           [e1, InertArgs Func [InertName "Branches",
                                                InertArgs ExpSeq bs]]]) =
    Case (maple2AST e1) (map branch bs)

maple2AST (InertArgs Func [InertName "Plate",
                           InertArgs ExpSeq [e1, InertName x, e2]]) =
    Plate x (maple2AST e1) (maple2AST e2)

maple2AST (InertArgs Func [f, (InertArgs ExpSeq a)]) =
    foldl App (maple2AST f) (map maple2AST a)

maple2AST (InertArgs Sum_ es) = NaryOp Sum (map maple2AST es)

maple2AST (InertArgs Product es) = NaryOp Prod (map maple2AST es)

maple2AST (InertArgs Less es) =
    foldl App (Var "less") (map maple2AST es)

maple2AST (InertArgs Equal es) =
    foldl App (Var "equal") (map maple2AST es)

-- Add special case for NatPow for Power
maple2AST (InertArgs Power [x, y]) =
    App (App (Var "**") (maple2AST x)) (maple2AST y)
maple2AST (InertArgs Rational [InertNum _ x, InertNum _ y]) =
    ULiteral $ Real $ fromInteger x / fromInteger y

maple2AST x = error $ "Can't handle: " ++ show x

mapleDatum2AST :: Text -> InertExpr -> AST' Text
mapleDatum2AST "pair" d = let [x, y] = unPairDatum d in
                          Pair (maple2AST x) (maple2AST y)
mapleDatum2AST "unit" _ = Unit
mapleDatum2AST h _ = error ("TODO: mapleDatum " ++ Text.unpack h)
    
maple2Type :: InertExpr -> TypeAST'
maple2Type (InertArgs Func
            [InertName "HInt",
             InertArgs ExpSeq
             [InertArgs Func
              [InertName "Bound",
               InertArgs ExpSeq
               [InertName ">=",InertNum Pos 0]]]])
    = TypeVar "nat"
maple2Type (InertArgs Func
            [InertName "HInt",
             InertArgs ExpSeq []])
    = TypeVar "int"
maple2Type (InertArgs Func
            [InertName "HReal",
             InertArgs ExpSeq
             [InertArgs Func
              [InertName "Bound",
               InertArgs ExpSeq
               [InertName ">=",InertNum Pos 0]]]])
    = TypeVar "prob"
maple2Type (InertArgs Func
            [InertName "HReal",
             InertArgs ExpSeq []])
    = TypeVar "real"
maple2Type x = error ("TODO: maple2Type " ++ show x)

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
  PData' (DV "pair" (map maple2Pattern (unpairPat args)))
maple2Pattern e = error ("TODO: maple2AST{pattern} " ++ show e)

unPairDatum :: InertExpr -> [InertExpr]
unPairDatum (InertArgs Func [InertName "Inl",
 InertArgs ExpSeq
 [InertArgs Func
  [InertName "Et",
   InertArgs ExpSeq
   [InertArgs Func
    [InertName "Konst",
     InertArgs ExpSeq [x]],
    InertArgs Func
    [InertName "Et",
     InertArgs ExpSeq
     [InertArgs Func
      [InertName "Konst",
       InertArgs ExpSeq [y]],
      InertName "Done"]]]]]]) = [x,y]
unPairDatum _ = error "pair has malformed constructors"

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

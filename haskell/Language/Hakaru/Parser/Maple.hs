{-# LANGUAGE CPP, OverloadedStrings, LambdaCase #-}
{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
module Language.Hakaru.Parser.Maple where

import           Prelude             hiding (not, and, sum, product)
import           Control.Monad.Identity
import           Data.Text           (Text)
import qualified Data.Text           as Text
import           Data.Ratio
#if __GLASGOW_HASKELL__ < 710
import           Data.Functor        ((<$>))
import           Control.Applicative (Applicative(..))
#endif
import           Text.Parsec
import           Text.Parsec.Text
import qualified Text.Parsec.Token   as Token
import           Text.Parsec.Language

import           Language.Hakaru.Parser.AST hiding (Less, Equal)

----------------------------------------------------------------

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

type TokenParser a = Token.GenTokenParser Text a Identity

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

symTable :: [(Text, Text)]
symTable =
    [ ("Gaussian",    "normal")
    , ("BetaD",       "beta")
    , ("GammaD",      "gamma")
    , ("PoissonD",    "poisson")
    , ("Weight",      "weight")
    , ("Lebesgue",    "lebesgue")
    , ("Counting",    "counting")
    , ("Uniform",     "uniform")
    , ("Ret",         "dirac")
    , ("Categorical", "categorical")
    , ("Geometric",   "geometric")
    , ("Not",         "not")
    , ("Pi",          "pi")
    , ("ln",          "log")
    , ("Beta",        "betaFunc")
    , ("GAMMA",       "gammaFunc")
    , ("csgn",        "signum")
    -- Type symbols
    , ("Real",        "real")
    , ("Prob",        "prob")
    , ("Measure",     "measure")
    , ("Bool",        "bool")
    ]

rename :: Text -> Text
rename x =
    case lookup x symTable of
    Just x' -> x'
    Nothing -> x

arg :: Parser a -> Parser [a]
arg e = parens (commaSep e)

text :: Text -> Parser Text
text = liftM Text.pack <$> string <$> Text.unpack

----------------------------------------------------------------
-- | Grammar of Inert Expressions

data NumOp = Pos | Neg
    deriving (Eq, Show)

data ArgOp
    = Float | Power  | Rational
    | Func  | ExpSeq | Sum_
    | Prod_ | Less   | Equal
    | NotEq | Not_   | And_
    | Range | List
    deriving (Eq, Show)

data InertExpr
    = InertName Text
    | InertNum  NumOp Integer
    | InertArgs ArgOp [InertExpr]
    deriving (Eq, Show)

----------------------------------------------------------------
-- Parsing String into Inert Expression

func :: Parser InertExpr
func =
    InertArgs
    <$> (text "_Inert_FUNCTION" *> return Func)
    <*> arg expr

name :: Parser InertExpr
name =
    InertName
    <$> (text "_Inert_NAME" *> parens stringLiteral)

localname :: Parser InertExpr
localname =
    InertName
    <$> (text "_Inert_LOCALNAME"
        *> parens
            (  stringLiteral
            <* comma
            <* integer))

assignedname :: Parser InertExpr
assignedname =
    InertName
    <$> (text "_Inert_ASSIGNEDNAME"
        *> parens
            (  stringLiteral
            <* comma
            <* stringLiteral))

assignedlocalname :: Parser InertExpr
assignedlocalname =
    InertName
    <$> (text "_Inert_ASSIGNEDLOCALNAME"
        *> parens
            (  stringLiteral
            <* comma
            <* stringLiteral
            <* comma
            <* integer))

expseq :: Parser InertExpr
expseq =
    InertArgs
    <$> (text "_Inert_EXPSEQ" *> return ExpSeq)
    <*> arg expr

intpos :: Parser InertExpr
intpos =
    InertNum
    <$> (text "_Inert_INTPOS" *> return Pos)
    <*> parens integer

intneg :: Parser InertExpr
intneg =
    InertNum
    <$> (text "_Inert_INTNEG" *> return Neg)
    <*> fmap negate (parens integer)

float :: Parser InertExpr
float  =
    InertArgs
    <$> (text "_Inert_FLOAT" *> return Float)
    <*> arg expr

power :: Parser InertExpr
power =
    InertArgs
    <$> (text "_Inert_POWER" *> return Power)
    <*> arg expr

range :: Parser InertExpr
range =
    InertArgs
    <$> (text "_Inert_RANGE" *> return Range)
    <*> arg expr

and :: Parser InertExpr
and =
    InertArgs
    <$> (text "_Inert_AND" *> return And_)
    <*> arg expr

list :: Parser InertExpr
list =
    InertArgs
    <$> (text "_Inert_LIST" *> return List)
    <*> arg expr

sum :: Parser InertExpr
sum =
    InertArgs
    <$> (text "_Inert_SUM" *> return Sum_)
    <*> arg expr

product :: Parser InertExpr
product =
    InertArgs
    <$> (text "_Inert_PROD" *> return Prod_)
    <*> arg expr

rational :: Parser InertExpr
rational =
    InertArgs
    <$> (text "_Inert_RATIONAL" *> return Rational)
    <*> arg expr

lessthan :: Parser InertExpr
lessthan =
    InertArgs
    <$> (text "_Inert_LESSTHAN" *> return Less)
    <*> arg expr

not :: Parser InertExpr
not =
    InertArgs
    <$> (text "_Inert_NOT" *> return Not_)
    <*> arg expr

lesseq :: Parser InertExpr
lesseq = do
    text "_Inert_LESSEQ"
    args <- arg expr
    return $ InertArgs Not_
               [ InertArgs Less (reverse args)]

equal :: Parser InertExpr
equal =
    InertArgs
    <$> (text "_Inert_EQUATION" *> return Equal)
    <*> arg expr

noteq :: Parser InertExpr
noteq =
    InertArgs
    <$> (text "_Inert_INEQUAT" *> return NotEq)
    <*> arg expr

expr :: Parser InertExpr
expr =  try func
    <|> try name
    <|> try list
    <|> try and
    <|> try not
    <|> try lessthan
    <|> try lesseq
    <|> try equal
    <|> try noteq
    <|> try assignedname
    <|> try assignedlocalname
    <|> try localname
    <|> try expseq
    <|> try intpos
    <|> try intneg
    <|> try range
    <|> try power
    <|> try sum
    <|> try product
    <|> try rational
    <|> float

parseMaple :: Text -> Either ParseError InertExpr
parseMaple txt =
    runParser (expr <* eof) () (Text.unpack txt) (Text.filter (/= '\n') txt)

----------------------------------------------------------------
-- Parsing InertExpr to AST' Text

collapseNaryOp :: NaryOp -> [AST' Text] -> [AST' Text]
collapseNaryOp op =
    concatMap (\case
                NaryOp op' e | op == op' ->  e
                t                        -> [t])


maple2AST :: InertExpr -> AST' Text
maple2AST (InertNum Pos i)       = ULiteral $ Nat $ fromInteger i
maple2AST (InertNum Neg i)       = ULiteral $ Int $ fromInteger i
maple2AST (InertName "infinity") = Infinity'
maple2AST (InertName t)          = Var (rename t)

maple2AST (InertArgs Float [InertNum Pos a, InertNum _ b]) = 
    ULiteral . Prob $ fromInteger a * (10 ^ b)

maple2AST (InertArgs Float [InertNum Neg a, InertNum _ b]) = 
    ULiteral . Real $ fromInteger a * (10 ^ b)

maple2AST (InertArgs Func
        [InertName "Let", InertArgs ExpSeq [e1, InertName x, e2]]) =
    Let x (maple2AST e1) (maple2AST e2)

maple2AST (InertArgs Func
        [InertName "Bind", InertArgs ExpSeq [e1, InertName x, e2]]) =
    Bind x (maple2AST e1) (maple2AST e2)

maple2AST (InertArgs Func
        [InertName "Datum", InertArgs ExpSeq [InertName h, d]]) =
    mapleDatum2AST h d

maple2AST (InertArgs Func [InertName "Lebesgue", _]) =
    Var "lebesgue"

maple2AST (InertArgs Func [InertName "Counting", _]) =
    Var "counting"

maple2AST (InertArgs Func
        [InertName "lam", InertArgs ExpSeq [InertName x, typ, e1]]) =
    Lam x (maple2Type typ) (maple2AST e1)

maple2AST (InertArgs Func
        [InertName "app", InertArgs ExpSeq [e1, e2]]) =
    App (maple2AST e1) (maple2AST e2)

maple2AST (InertArgs Func
        [InertName "NegativeBinomial", InertArgs ExpSeq [e1, e2]]) =
    Bind "i" (op2 "gamma" r (recip_ $ recip_ p -. (lit $ Prob 1)))
         (App (Var "poisson") (Var "i"))
    where recip_     = App (Var "recip")
          x -. y     = NaryOp Sum [x, App (Var "negate") y]
          op2  s x y = App (App (Var s) x) y
          lit        = ULiteral
          r          = maple2AST e1
          p          = maple2AST e2

maple2AST (InertArgs Func
        [InertName "Msum", InertArgs ExpSeq []]) =
    Var "reject"

maple2AST (InertArgs Func
        [InertName "Msum", InertArgs ExpSeq es]) =
    Msum (map maple2AST es)

maple2AST (InertArgs Func
        [InertName "ary", InertArgs ExpSeq [e1, InertName x, e2]]) =
    Array x (maple2AST e1) (maple2AST e2)

maple2AST (InertArgs Func
        [InertName "idx", InertArgs ExpSeq [e1, e2]]) =
    Index (maple2AST e1) (maple2AST e2)

maple2AST (InertArgs Func
        [InertName "piecewise", InertArgs ExpSeq es]) = go es where
  go [e1,e2]      = If (maple2AST e1) (maple2AST e2) (ULiteral (Nat 0))
  go [e1,e2,e3]   = If (maple2AST e1) (maple2AST e2) (maple2AST e3)
  go [e1,e2,_,e3] = If (maple2AST e1) (maple2AST e2) (maple2AST e3)
  go (e1:e2:rest) = If (maple2AST e1) (maple2AST e2) (go rest)

maple2AST (InertArgs Func
        [InertName "max", InertArgs ExpSeq es]) =
    NaryOp Max (map maple2AST es)

maple2AST (InertArgs Func
        [InertName "min", InertArgs ExpSeq es]) =
    NaryOp Min (map maple2AST es)

maple2AST (InertArgs Func
        [InertName "Ei", InertArgs ExpSeq [e1, e2]]) =
    Integrate "t" (maple2AST e2) Infinity'
    (NaryOp Prod [ App (Var "exp")   (App (Var "negate") (Var "t"))
                 , App (Var "recip")
                       (App (App (Var "^") (Var "t")) (maple2AST e1))
                 ])

maple2AST (InertArgs Func
        [ InertName "case"
        , InertArgs ExpSeq
            [e1, InertArgs Func
                [ InertName "Branches"
                , InertArgs ExpSeq bs]]]) =
    Case (maple2AST e1) (map branch bs)

maple2AST (InertArgs Func
        [InertName "Plate", InertArgs ExpSeq [e1, InertName x, e2]]) =
    Plate x (maple2AST e1) (maple2AST e2)

maple2AST (InertArgs Func
        [InertName "And", InertArgs ExpSeq es]) =
    NaryOp And (map maple2AST es)

maple2AST (InertArgs Func
        [ InertName "int"
        , InertArgs ExpSeq
           [ f
           , InertArgs Equal
             [ InertName x
             , InertArgs Range [lo, hi]]]]) =
    Integrate x (maple2AST lo) (maple2AST hi) (maple2AST f)

maple2AST (InertArgs Func
        [ InertName "Int"
        , InertArgs ExpSeq
           [ f
           , InertArgs Equal
             [ InertName x
             , InertArgs Range [lo, hi]]]]) =
    Integrate x (maple2AST lo) (maple2AST hi) (maple2AST f)

maple2AST (InertArgs Func
        [ InertName "SumIE"
        , InertArgs ExpSeq
           [ f
           , InertArgs Equal
             [ InertName x
             , InertArgs Range [lo, hi]]]]) =
    Summate x (maple2AST lo) (maple2AST hi) (maple2AST f)

maple2AST (InertArgs Func
        [ InertName "ProductIE"
        , InertArgs ExpSeq
           [ f
           , InertArgs Equal
             [ InertName x
             , InertArgs Range [lo, hi]]]]) =
    Product x (maple2AST lo) (maple2AST hi) (maple2AST f)

maple2AST (InertArgs Func
        [ InertName "BucketIE"
        , InertArgs ExpSeq
           [ f
           , InertArgs Equal
             [ InertName x
             , InertArgs Range [lo, hi]]]]) =
    Bucket x (maple2AST lo) (maple2AST hi) (maple2ReducerAST f)

maple2AST (InertArgs Func
        [f, InertArgs ExpSeq es]) =
    foldl App (maple2AST f) (map maple2AST es)

maple2AST (InertArgs List [InertArgs ExpSeq es]) = ArrayLiteral $ map maple2AST es

maple2AST (InertArgs And_  es) = NaryOp And  (collapseNaryOp And  (map maple2AST es))
maple2AST (InertArgs Sum_  es) = NaryOp Sum  (collapseNaryOp Sum  (map maple2AST es))
maple2AST (InertArgs Prod_ es) = NaryOp Prod (collapseNaryOp Prod (map maple2AST es))

maple2AST (InertArgs Not_ [e])  =
    App (Var "not") (maple2AST e)

maple2AST (InertArgs Less es)  =
    foldl App (Var "less")  (map maple2AST es)

maple2AST (InertArgs Equal es) =
    foldl App (Var "equal") (map maple2AST es)

maple2AST (InertArgs NotEq es) =
    App (Var "not") (foldl App (Var "equal") (map maple2AST es))

maple2AST (InertArgs Power [x, InertNum Pos y]) =
    App (App (Var "^")  (maple2AST x)) (maple2AST (InertNum Pos y))
maple2AST (InertArgs Power [x, InertNum Neg (-1)]) =
    App (Var "recip")  (maple2AST x)
maple2AST (InertArgs Power [x, 
                            InertArgs Rational
                            [InertNum Pos 1, InertNum Pos y]]) =
    App (App (Var "natroot") (maple2AST x)) (ULiteral . Nat $ y)

maple2AST (InertArgs Power [x, 
                            InertArgs Rational
                            [InertNum Neg (-1), InertNum Pos y]]) =
    App (Var "recip")
        (App (App (Var "natroot") (maple2AST x)) (ULiteral . Nat $ y))

maple2AST (InertArgs Power [x, y]) =
    App (App (Var "**") (maple2AST x)) (maple2AST y)
maple2AST (InertArgs Rational [InertNum Pos x, InertNum Pos y]) =
    ULiteral . Prob $ fromInteger x % fromInteger y
maple2AST (InertArgs Rational [InertNum _ x, InertNum _ y]) =
    ULiteral . Real $ fromInteger x % fromInteger y

maple2AST x = error $ "Can't handle: " ++ show x

----------------------------------------------------------------

maple2ReducerAST :: InertExpr -> Reducer' Text
maple2ReducerAST
 (InertArgs Func
  [ InertName "Fanout"
  , InertArgs ExpSeq [ e1, e2 ]]) =
  R_Fanout (maple2ReducerAST e1) (maple2ReducerAST e2)

maple2ReducerAST
 (InertArgs Func
  [ InertName "Index"
  , InertArgs ExpSeq [ e1, InertName x, e2, e3]]) =
  R_Index x (maple2AST e1) (maple2AST e2) (maple2ReducerAST e3)

maple2ReducerAST
 (InertArgs Func
  [ InertName "Split"
  , InertArgs ExpSeq [ e1, e2, e3]]) =
  R_Split (maple2AST e1) (maple2ReducerAST e2) (maple2ReducerAST e3)

maple2ReducerAST
 (InertArgs Func
  [ InertName "Nop"
  , InertArgs ExpSeq []]) = R_Nop

maple2ReducerAST
 (InertArgs Func
  [ InertName "Add"
  , InertArgs ExpSeq [e1]]) = R_Add (maple2AST e1)

mapleDatum2AST :: Text -> InertExpr -> AST' Text
mapleDatum2AST h d = case (h, maple2DCode d) of
  ("pair", [x,y]) -> Pair x y
  ("unit", []   ) -> Unit
  _               -> error $ "TODO: mapleDatum2AST " ++ Text.unpack h
    
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

maple2Type (InertArgs Func
            [InertName "HData",
             InertArgs ExpSeq
             [InertArgs Func
              [InertName "DatumStruct",
               InertArgs ExpSeq
               [InertName "unit",
                InertArgs List
                [InertArgs ExpSeq []]]]]])
     = TypeVar "unit"

maple2Type (InertArgs Func
            [InertName "HData",
             InertArgs ExpSeq
             [InertArgs Func
              [InertName "DatumStruct",
               InertArgs ExpSeq
               [InertName "true",
                InertArgs List
                [InertArgs ExpSeq []]]],
              InertArgs Func
              [InertName "DatumStruct",
               InertArgs ExpSeq
               [InertName "false",
                InertArgs List
                [InertArgs ExpSeq []]]]]])
     = TypeVar "bool"

maple2Type (InertArgs Func
            [InertName "HData",
             InertArgs ExpSeq
             [InertArgs Func
              [InertName "DatumStruct",
               InertArgs ExpSeq
               [InertName "pair",
                InertArgs List
                [InertArgs ExpSeq
                 [InertArgs Func
                  [InertName "Konst",
                   InertArgs ExpSeq [x]],
                  InertArgs Func
                  [InertName "Konst",
                   InertArgs ExpSeq [y]]]]]]]])
     = TypeApp "pair" (map maple2Type [x, y])

maple2Type (InertArgs Func
            [InertName "HArray",
             InertArgs ExpSeq
             [x]])
     = TypeApp "array" [maple2Type x]

maple2Type (InertArgs Func
            [InertName "HFunction",
             InertArgs ExpSeq
             [x, y]])
     = TypeFun (maple2Type x) (maple2Type y)

maple2Type (InertArgs Func
            [InertName "HMeasure",
             InertArgs ExpSeq
             [x]])
     = TypeApp "measure" [maple2Type x]

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
                [InertName hint, args]]) =
    PData' (DV hint (maple2Patterns args))
maple2Pattern e = error $ "TODO: maple2AST{pattern} " ++ show e

maple2DCode :: InertExpr -> [AST' Text]
maple2DCode (InertArgs Func [InertName "Inl", InertArgs ExpSeq [e]]) = maple2DCode e
maple2DCode (InertArgs Func [InertName "Inr", InertArgs ExpSeq [e]]) = maple2DCode e
maple2DCode (InertArgs Func [InertName "Et" , InertArgs ExpSeq [InertArgs Func [InertName "Konst", InertArgs ExpSeq [x]], e]]) = maple2AST x : maple2DCode e
maple2DCode (InertName "Done") = []
maple2DCode e = error $ "maple2DCode: " ++ show e ++ " not InertExpr of a datum"

maple2Patterns :: InertExpr -> [Pattern' Text]
maple2Patterns (InertArgs Func [InertName "PInl", InertArgs ExpSeq [e]]) = maple2Patterns e
maple2Patterns (InertArgs Func [InertName "PInr", InertArgs ExpSeq [e]]) = maple2Patterns e
maple2Patterns (InertArgs Func [InertName "PEt" , InertArgs ExpSeq [InertArgs Func [InertName "PKonst", InertArgs ExpSeq [x]], e]]) = maple2Pattern x : maple2Patterns e
maple2Patterns (InertName "PDone") = []
maple2Patterns e = error $ "maple2Patterns: " ++ show e ++ " not InertExpr of a pattern"

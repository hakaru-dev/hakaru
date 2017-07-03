{-# LANGUAGE CPP, OverloadedStrings #-}
{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
module Language.Hakaru.Parser.Parser (parseHakaru, parseHakaruWithImports) where

import Prelude hiding (Real)

#if __GLASGOW_HASKELL__ < 710
import           Data.Functor                  ((<$>), (<$))
import           Control.Applicative           (Applicative(..))
#endif
import           Data.Functor.Identity
import           Data.Text                     (Text)
import qualified Data.Text                     as Text
import           Data.Ratio                    ((%))
import           Data.Char                     (digitToInt)
import           Text.Parsec
import           Text.Parsec.Text              () -- instances only
import           Text.Parsec.Indentation
import           Text.Parsec.Indentation.Char
import qualified Text.Parsec.Indentation.Token as ITok
import           Text.Parsec.Expr              (Assoc(..), Operator(..))
import qualified Text.Parsec.Token             as Tok

import Language.Hakaru.Parser.AST

ops, names :: [String]
ops = words "^ ** * / + - .  < > <= >= == /= && || <|> -> : <~ = _"
names = concatMap words [ "def fn"
                        , "if else match"
                        , "expect observe"
                        , "return dirac"
                        , "integrate summate product from to"
                        , "array plate chain of"
                        , "import data ∞" ]

type ParserStream    = IndentStream (CharIndentStream Text)
type Parser          = ParsecT     ParserStream () Identity
type OperatorTable a = [[Operator ParserStream () Identity a]]

style :: Tok.GenLanguageDef ParserStream st Identity
style = ITok.makeIndentLanguageDef $ Tok.LanguageDef
    { Tok.commentStart    = ""
    , Tok.commentEnd      = ""
    , Tok.nestedComments  = True
    , Tok.identStart      = letter <|> char '_'
    , Tok.identLetter     = alphaNum <|> oneOf "_'"
    , Tok.opStart         = oneOf [ c | c:_ <- ops ]
    , Tok.opLetter        = oneOf [ c | _:cs <- ops, c <- cs ]
    , Tok.caseSensitive   = True
    , Tok.commentLine     = "#"
    , Tok.reservedOpNames = ops
    , Tok.reservedNames   = names
    }

lexer :: Tok.GenTokenParser ParserStream () Identity
lexer = ITok.makeTokenParser style

whiteSpace :: Parser ()
whiteSpace = Tok.whiteSpace lexer

decimal :: Parser Integer
decimal = Tok.decimal lexer

decimalFloat :: Parser Literal'
decimalFloat = do n <- decimal
                  option (Nat n) (Prob <$> fractExponent n)

fractExponent   :: Integer -> Parser Rational
fractExponent n =  do{ fract <- fraction
                     ; expo  <- option 1 exponent'
                     ; return ((fromInteger n + fract)*expo)
                     }
                  <|>
                  do{ expo <- exponent'
                    ; return ((fromInteger n)*expo)
                    }

fraction        :: Parser Rational
fraction        =  do{ d      <- try (char '.' *> digit)
                     ; digits <- many digit <?> "fraction"
                     ; return (foldr1 op (map (fromIntegral.digitToInt) (d:digits))
                               / 10)
                     }
                  <?> "fraction"
                    where
                      op d f    = d + f / 10

exponent'       :: Parser Rational
exponent'       =  do{ _ <- oneOf "eE"
                     ; f <- (negate <$ char '-') <|> (id <$ optional (char '+'))
                     ; e <- decimal <?> "exponent"
                     ; return (10 ^^ f e)
                     }
                  <?> "exponent"

parens :: Parser a -> Parser a
parens = Tok.parens lexer . localIndentation Any

brackets :: Parser a -> Parser a
brackets = Tok.brackets lexer . localIndentation Any

commaSep :: Parser a -> Parser [a]
commaSep = Tok.commaSep lexer

identifier :: Parser Text
identifier = Text.pack <$> Tok.identifier lexer

reserved :: String -> Parser ()
reserved s
  | s `elem` names -- assertion
  = Tok.reserved lexer s
  | otherwise
  = error ("Parser failed to reserve the name " ++ show s)

reservedOp :: String -> Parser ()
reservedOp s
  | s `elem` ops -- assertion
  = Tok.reservedOp lexer s
  | otherwise
  = error ("Parser failed to reserve the operator " ++ show s)

app1 :: a -> AST' a -> AST' a
app1 s x = Var s `App` x

app2 :: a -> AST' a -> AST' a -> AST' a
app2 s x y = Var s `App` x `App` y

divide, sub :: AST' Text -> AST' Text -> AST' Text
divide       (WithMeta (ULiteral (Nat   x     )) (SourceSpan s _))
             (WithMeta (ULiteral (Nat       y )) (SourceSpan _ e))
           = (WithMeta (ULiteral (Prob (x % y))) (SourceSpan s e))
divide x y = NaryOp Prod [x, app1 "recip" y]
sub    x y = NaryOp Sum  [x, app1 "negate" y]

bi :: ([a] -> b) -> a -> a -> b
bi f x y = f [x, y]

negate_rel :: (AST' Text -> AST' Text -> AST' Text)
           -> (AST' Text -> AST' Text -> AST' Text)
negate_rel f x y = app1 "not" (f x y)

binary :: String
       -> Assoc
       -> (a -> a -> a)
       -> Operator ParserStream () Identity a
binary s a f = Infix (f <$ reservedOp s) a

postfix :: Stream s m t
        => ParsecT s u m (AST' a -> AST' a)
        -> Operator s u m (AST' a)
postfix p = Postfix (chainl1 p' (return (flip (.))))
  where p' = do f <- p
                e <- getPosition
                return (\x -> case x of
                  WithMeta _ (SourceSpan s _) -> WithMeta (f x) (SourceSpan s e)
                  _                           ->           f x)

sign :: Parser (AST' Text -> AST' Text)
sign = do
  s <- getPosition
  (fNat, fProb, fRest)
    <- ((id    , id    , id           ) <$ reservedOp "+") <|>
       ((negate, negate, app1 "negate") <$ reservedOp "-")
  let f     (WithMeta (ULiteral (Nat         x )) (SourceSpan _ e))
          = (WithMeta (ULiteral (Int  (fNat  x))) (SourceSpan s e))
      f     (WithMeta (ULiteral (Prob        x )) (SourceSpan _ e))
          = (WithMeta (ULiteral (Real (fProb x))) (SourceSpan s e))
      f x = fRest x
  return f

table :: OperatorTable (AST' Text)
table = [ [ postfix (array_index <|> fun_call) ]
        , [ binary "^"   AssocRight $ app2 "^"
          , binary "**"  AssocRight $ app2 "**" ]
        , [ binary "*"   AssocLeft  $ bi (NaryOp Prod)
          , binary "/"   AssocLeft  $ divide ]
        , [ Prefix sign
          , binary "+"   AssocLeft  $ bi (NaryOp Sum)
          , binary "-"   AssocLeft  $ sub ]
        , [ postfix ann_expr ]
        , [ binary "<"   AssocNone  $                     app2 "less"
          , binary ">"   AssocNone  $              flip $ app2 "less"
          , binary "<="  AssocNone  $ negate_rel $ flip $ app2 "less"
          , binary ">="  AssocNone  $ negate_rel $        app2 "less"
          , binary "=="  AssocNone  $                     app2 "equal"
          , binary "/="  AssocNone  $ negate_rel $        app2 "equal" ]
        , [ binary "&&"  AssocRight $ bi (NaryOp And) ]
        , [ binary "||"  AssocRight $ bi (NaryOp Or) ]
        , [ binary "<|>" AssocRight $ bi Msum ] ]

natOrProb :: Parser (AST' a)
natOrProb = (ULiteral <$> decimalFloat) <* whiteSpace

inf_ :: Parser (AST' a)
inf_ = reserved "∞" *> return Infinity'

var :: Parser (AST' Text)
var = Var <$> identifier

parenthesized :: Parser (AST' Text)
parenthesized = f <$> parens (commaSep expr)
  where f [] = Unit
        f xs = foldr1 Pair xs

type_var_or_app :: Parser TypeAST'
type_var_or_app = do x <- ("array" <$ reserved "array") <|> identifier
                     option (TypeVar x) (TypeApp x <$> parens (commaSep type_expr))

type_expr :: Parser TypeAST'
type_expr = foldr1 TypeFun <$> sepBy1 (parens type_expr <|> type_var_or_app)
                                      (reservedOp "->")

ann_expr :: Parser (AST' Text -> AST' Text)
ann_expr = reservedOp "." *> (flip Ann <$> type_expr)

pdat_expr :: Parser (PDatum Text)
pdat_expr = DV <$> identifier <*> parens (commaSep pat_expr)

pat_expr :: Parser (Pattern' Text)
pat_expr =  try (PData' <$> pdat_expr)
        <|> (PData' <$> (DV "pair" <$> parens (commaSep pat_expr)))
        <|> (PWild' <$  reservedOp "_")
        <|> (PVar'  <$> identifier)


-- | Blocks are indicated by colons, and must be indented.
blockOfMany :: Parser a -> Parser [a]
blockOfMany p = do
    reservedOp ":"
    localIndentation Gt (many $ absoluteIndentation p)


-- | Semiblocks are like blocks, but indentation is optional. Also,
-- there are only 'expr' semiblocks.
semiblockExpr :: Parser (AST' Text)
semiblockExpr = reservedOp ":"
                *> localIndentation Ge (absoluteIndentation expr)


branch_expr :: Parser (Branch' Text)
branch_expr = Branch' <$> pat_expr <* reservedOp ":"
              <*> localIndentation Gt expr

match_expr :: Parser (AST' Text)
match_expr = Case <$ reserved "match" <*> expr <* reservedOp ":"
             <*> localIndentation Ge (many (absoluteIndentation branch_expr))

integrate_expr :: Parser (AST' Text)
integrate_expr =
    reserved "integrate"
    *> (Integrate
        <$> identifier
        <*  reserved "from"
        <*> expr
        <*  reserved "to"
        <*> expr
        <*> semiblockExpr
        )

summate_expr :: Parser (AST' Text)
summate_expr =
    reserved "summate"
    *> (Summate
        <$> identifier
        <*  reserved "from"
        <*> expr
        <*  reserved "to"
        <*> expr
        <*> semiblockExpr
        )

product_expr :: Parser (AST' Text)
product_expr =
    reserved "product"
    *> (Product
        <$> identifier
        <*  reserved "from"
        <*> expr
        <*  reserved "to"
        <*> expr
        <*> semiblockExpr
        )

expect_expr :: Parser (AST' Text)
expect_expr =
    reserved "expect"
    *> (Expect
        <$> identifier
        <*> expr
        <*> semiblockExpr
        )

observe_expr :: Parser (AST' Text)
observe_expr =
    reserved "observe"
    *> (Observe
        <$> expr
        <*> expr
        )

array_expr :: Parser (AST' Text)
array_expr =
    reserved "array"
    *> (Array
        <$> identifier
        <*  reserved "of"
        <*> expr
        <*> semiblockExpr
        )

array_index :: Parser (AST' Text -> AST' Text)
array_index = flip Index <$> brackets expr

array_literal :: Parser (AST' Text)
array_literal = ArrayLiteral <$> brackets (commaSep expr)

plate_expr :: Parser (AST' Text)
plate_expr =
    reserved "plate"
    *> (Plate
        <$> identifier
        <*  reserved "of"
        <*> expr
        <*> semiblockExpr
        )

chain_expr :: Parser (AST' Text)
chain_expr =
    reserved "chain"
    *> (Chain
        <$> identifier
        <*> expr
        <*> expr
        <*> semiblockExpr
        )


if_expr :: Parser (AST' Text)
if_expr = If <$ reserved "if" <*> expr <*> semiblockExpr <*
          reserved "else" <*> semiblockExpr

lam_expr :: Parser (AST' Text)
lam_expr =
    reserved "fn"
    *>  (Lam
        <$> identifier
        <*> type_expr
        <*> semiblockExpr
        )

bind_expr :: Parser (AST' Text)
bind_expr = localIndentation Ge
  (absoluteIndentation (try (Bind <$> identifier <* reservedOp "<~")
   <*> localIndentation Gt expr)
   <*> absoluteIndentation expr)

let_expr :: Parser (AST' Text)
let_expr = localIndentation Ge
  (absoluteIndentation (try (Let <$> identifier <* reservedOp "=")
   <*> localIndentation Gt expr)
   <*> absoluteIndentation expr)

def_expr :: Parser (AST' Text)
def_expr = localIndentation Ge $ do
    absoluteIndentation (reserved "def")
    name <- identifier
    vars <- parens (commaSep defarg)
    bodyTyp <- optionMaybe type_expr
    reservedOp ":"
    body    <- localIndentation Gt expr
    let body' = foldr (\(var', varTyp) e -> Lam var' varTyp e) body vars
        typ   = foldr TypeFun <$> bodyTyp <*> return (map snd vars)
    Let name (maybe id (flip Ann) typ body')
        <$> absoluteIndentation expr -- the \"rest\"; i.e., where the 'def' is in scope

defarg :: Parser (Text, TypeAST')
defarg = (,) <$> identifier <*> type_expr

fun_call :: Parser (AST' Text -> AST' Text)
fun_call = flip (foldl App) <$> parens (commaSep expr)

return_expr :: Parser (AST' Text)
return_expr = do
    reserved "return" <|> reserved "dirac"
    app1 "dirac" <$> expr

term :: Parser (AST' Text)
term =  if_expr
    <|> return_expr
    <|> lam_expr
    <|> def_expr
    <|> match_expr
    <|> data_expr
    <|> integrate_expr
    <|> summate_expr
    <|> product_expr
    <|> expect_expr
    <|> observe_expr
    <|> array_expr
    <|> plate_expr
    <|> chain_expr
    <|> let_expr
    <|> bind_expr
    <|> array_literal
    <|> inf_
    <|> natOrProb
    <|> var
    <|> parenthesized
    <?> "simple expression"

expr :: Parser (AST' Text)
expr = withPos (buildExpressionParser table (withPos term) <?> "expression")


indentConfig :: Text -> ParserStream
indentConfig =
    mkIndentStream 0 infIndentation True Ge . mkCharIndentStream

parseHakaru :: Text -> Either ParseError (AST' Text)
parseHakaru = parseAtTopLevel expr

parseHakaruWithImports :: Text -> Either ParseError (ASTWithImport' Text)
parseHakaruWithImports = parseAtTopLevel exprWithImport

parseAtTopLevel :: Parser a -> Text -> Either ParseError a
parseAtTopLevel p =
    runParser (whiteSpace *>
               p <* eof) () "<input>" . indentConfig

withPos :: Parser (AST' a) -> Parser (AST' a)
withPos x = do
    s  <- getPosition
    x' <- x
    e  <- getPosition
    return $ WithMeta x' (SourceSpan s e)

{-
user-defined types:

data either(a,b):
  left(a)
  right(a)

data maybe(a):
  nothing
  just(a)
-}

data_expr :: Parser (AST' Text)
data_expr = do
    reserved "data"
    ident <- identifier
    typvars <- parens (commaSep identifier)
    ts <- blockOfMany type_var_or_app
    e <- expr
    return (Data ident typvars ts e)

import_expr :: Parser (Import Text)
import_expr =
    reserved "import" *> (Import <$> identifier)

exprWithImport :: Parser (ASTWithImport' Text)
exprWithImport = ASTWithImport' <$> (many import_expr) <*> expr

-- | A variant of @Text.Parsec.Expr.buildExpressionParser@ (parsec-3.1.11)
-- that behaves more restrictively when a precedence level contains both
-- unary and binary operators.  Unary operators are only allowed on the
-- first operand when parsing left-associatively and on the last operand
-- when parsing right-associatively.  This restriction lets us recover the
-- behavior of unary negation in Haskell.

buildExpressionParser :: (Stream s m t)
                      => [[Operator s u m a]]
                      -> ParsecT s u m a
                      -> ParsecT s u m a
buildExpressionParser operators simpleExpr
    = foldl (makeParser) simpleExpr operators
    where
      makeParser term ops
        = let (rassoc,lassoc,nassoc
               ,prefix,postfix)      = foldr splitOp ([],[],[],[],[]) ops

              rassocOp   = choice rassoc
              lassocOp   = choice lassoc
              nassocOp   = choice nassoc
              prefixOp   = choice prefix  <?> ""
              postfixOp  = choice postfix <?> ""

              ambigious assoc op= try $
                                  do{ _ <- op
                                    ; fail ("ambiguous use of a " ++ assoc
                                            ++ " associative operator")
                                    }

              ambigiousRight    = ambigious "right" rassocOp
              ambigiousLeft     = ambigious "left" lassocOp
              ambigiousNon      = ambigious "non" nassocOp

              termP      = do{ (preU, pre)   <- prefixP
                             ; x             <- term
                             ; (postU, post) <- postfixP
                             ; return (preU || postU, post (pre x))
                             }

              postfixP   = ((,) True) <$> postfixOp <|> return (False, id)

              prefixP    = ((,) True) <$> prefixOp <|> return (False, id)

              rassocP x  = do{ f      <- rassocOp
                             ; (u, z) <- termP
                             ; y      <- if u then return z else rassocP1 z
                             ; return (f x y)
                             }
                           <|> ambigiousLeft
                           <|> ambigiousNon
                           -- <|> return x

              rassocP1 x = rassocP x  <|> return x

              lassocP x  = do{ f <- lassocOp
                             ; y <- term
                             ; lassocP1 (f x y)
                             }
                           <|> ambigiousRight
                           <|> ambigiousNon
                           -- <|> return x

              lassocP1 x = lassocP x <|> return x

              nassocP x  = do{ f <- nassocOp
                             ; y <- term
                             ;    ambigiousRight
                              <|> ambigiousLeft
                              <|> ambigiousNon
                              <|> return (f x y)
                             }
                           -- <|> return x

           in  do{ (u, x) <- termP
                 ;     (if u then parserZero else rassocP x)
                   <|>                            lassocP x
                   <|> (if u then parserZero else nassocP x)
                   <|>                            return  x
                   <?> "operator"
                 }


      splitOp (Infix op assoc) (rassoc,lassoc,nassoc,prefix,postfix)
        = case assoc of
            AssocNone  -> (rassoc,lassoc,op:nassoc,prefix,postfix)
            AssocLeft  -> (rassoc,op:lassoc,nassoc,prefix,postfix)
            AssocRight -> (op:rassoc,lassoc,nassoc,prefix,postfix)

      splitOp (Prefix op) (rassoc,lassoc,nassoc,prefix,postfix)
        = (rassoc,lassoc,nassoc,op:prefix,postfix)

      splitOp (Postfix op) (rassoc,lassoc,nassoc,prefix,postfix)
        = (rassoc,lassoc,nassoc,prefix,op:postfix)

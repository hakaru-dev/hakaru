module PPrint where

import Text.PrettyPrint

type Var a = Int
type Exp a = Int -> Doc

lit :: (Show a) => a -> Exp a
lit x i = text (show x)

var :: Var a -> Exp a
var x i = text ("x" ++ show x)

dirac :: Exp a -> Exp b
dirac p i = text "dirac" <> parens (p i)

bern :: Exp a -> Exp b
bern p i = text "bern" <> parens (p i)

uniform :: Exp a -> Exp b -> Exp c
uniform lo hi i = text "uniform" <>
                  parens (lo i <> comma <> hi i)

normal :: Exp a -> Exp b -> Exp c
normal mu sd i = text "normal"  <> 
                 parens (mu i <> comma <> sd i)

categorical :: Exp a -> Exp b
categorical p i = text "categorical" <>
                  parens (p i)

bind :: Exp a -> (Exp a -> Exp b) -> Exp b
bind m cont i = text "let" <+>
                var i i <+>
                text "<-" <+>
                m i <+>
                text "in" $$
                cont (var i) (i+1)

conditioned :: Exp a -> Exp b
conditioned f i = text "observe" <> parens (f i)

unconditioned :: Exp a -> Exp b
unconditioned f = f

lam :: (Exp a -> Exp a) -> Exp (a -> b)
lam body i = parens (
               text "lambda" <+>
               var i i <+>
               text "->" <+> 
               body (var i) (i+1))

app :: Exp (a -> b) -> Exp a -> Exp b
app f x i = parens (f i <+> x i)

fix :: (Exp a -> Exp a) -> Exp a
fix g i = parens (
            text "fix" <+>
            var i i <+>
            text "->" <+>
            g (var i) (i+1))

ifThenElse :: Exp a -> Exp b -> Exp c -> Exp d
ifThenElse cond t f i = parens (
                          text "if" <+> cond i <+>
                          text "then" <+> t i <+>
                          text "else" <+> f i)

test :: Exp a
test = unconditioned (uniform (lit False) (lit True)) `bind`
       \c ->  conditioned (ifThenElse
                           c
                           (normal (lit 1) (lit 1))
                           (uniform (lit 0) (lit 3))) `bind`
              \_ ->  unconditioned (dirac c)

-- main :: IO ()
-- main = print $ test 0

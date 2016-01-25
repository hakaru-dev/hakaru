{-# LANGUAGE NoImplicitPrelude, DataKinds, TypeOperators #-}

module Tests.Expect where

import Prelude (($))
import qualified Data.Text as Text

import Language.Hakaru.Syntax.ABT      (ABT(..), TrivialABT)
import Language.Hakaru.Syntax.Variable (Variable(..))
import Language.Hakaru.Types.Sing
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Syntax.Prelude
import Language.Hakaru.Pretty.Haskell  (pretty)
import Language.Hakaru.Expect


-- | The main thing is that this should typecheck and not throw
-- errors. The easiest to obtain correct result is @lam $ \x -> sum
-- [x * prob_ 1]@. We used to return that, but then we simplified
-- it to return @lam $ \x -> x * prob_ 1@ by using smart constructors
-- for detecting unary NaryOps. We'd like to simplify that further
-- by recognizing that @x * prob_ 1 == x@ for all @x@.
--
-- Should return a program equivalent to @lam $ \x -> x@.
test1 :: TrivialABT Term '[] ('HProb ':-> 'HProb)
test1 = lam $ \x -> total (weight_ x)


-- | Again the main thing is that this should typecheck and not
-- throw errors. We'd rather use @lam $ \x -> total x@ but that
-- causes 'binder' to throw a @<<loop>>@ exception, because 'expect'
-- needs to force variable IDs to store them in the 'Assocs'.
--
-- Should do nothing, since there's nothing we can do to a free
-- variable. Notably, should resizualise the call to 'expect'.
test2 :: TrivialABT Term '[] ('HMeasure 'HProb ':-> 'HProb)
test2 = syn (Lam_ :$ bind x (total (var x)) :* End)
    where
    x = Variable (Text.pack "x") 2 (SMeasure SProb)
-- TODO: Is there any way to work around the problem so we don't
-- need to manually generate our own variable? Maybe by explicitly
-- using the 'Expect' primop, and then performing the evaluation
-- of that primop after 'binder' has finished constructing the
-- first-order AST; but how can we specify that order of evaluation
-- (except by making the evaluation of 'Expect' as 'expect' explicit)?


-- | Again the main thing is that this should typecheck and not
-- throw errors; and again, we'd rather use @lam $ \x -> total (x
-- `app` int_ 3)@
--
-- Should do nothing, because there's nothing we can do to a free
-- variable applied to some arguments. Again, should residualise
-- the call to 'expect'.
test3 :: TrivialABT Term '[] (('HInt ':-> 'HMeasure 'HProb) ':-> 'HProb)
test3 = syn (Lam_ :$ bind x (total (var x `app` int_ 3)) :* End)
    where
    x = Variable (Text.pack "x") 2 (SFun SInt $ SMeasure SProb)


-- | Should return the same thing as @total (dirac unit)@ (namely
-- @1@) by evaluating away the @if_ true@ part. Notably, the result
-- should not be affected by the 'weight' in the else branch.
test4 :: TrivialABT Term '[] 'HProb
test4 = total $ if_ true (dirac unit) (weight_ (prob_ 5) >> dirac unit)


test5 :: TrivialABT Term '[] (HEither HUnit HUnit ':-> 'HProb)
test5 =
    lam $ \x ->
        total $
            uneither x
            (\_ -> dirac unit)
            (\_ -> weight_ (prob_ 5) >> dirac unit)

{-
total (array (nat_ 1) (\x -> dirac x) ! nat_ 0) :: TrivialABT Term '[] 'HProb
syn (Literal_ (VProb 1.0))
-}

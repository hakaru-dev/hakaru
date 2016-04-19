{-# LANGUAGE NoImplicitPrelude, DataKinds, TypeOperators #-}

module Tests.Expect where

import Prelude (($), (.))
import qualified Data.Text as Text

import Language.Hakaru.Syntax.ABT      (ABT(..), TrivialABT)
import Language.Hakaru.Syntax.Variable (Variable(..))
import Language.Hakaru.Types.Sing
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Syntax.Prelude
import Language.Hakaru.Pretty.Haskell  (pretty)
import Language.Hakaru.Expect2
import Language.Hakaru.Evaluation.ConstantPropagation (constantPropagation)
import Language.Hakaru.Disintegrate (disintegrateWithVar)

-- | The main thing is that this should typecheck and not throw
-- errors. The easiest to obtain correct result is @lam $ \x -> sum
-- [x * prob_ 1]@. We used to return that, but then we simplified
-- it to return @lam $ \x -> x * prob_ 1@ by using smart constructors
-- for detecting unary NaryOps. We'd like to simplify that further
-- by recognizing that @x * prob_ 1 == x@ for all @x@.
--
-- Should return a program equivalent to @lam $ \x -> x@.
--
-- BUG: this seems to work fine for the old @Expect.hs@ but it loops
-- forever with the new @Expect2.hs@. This appears to be due to the
-- use of 'binder' in 'lam', since 'test1b' works fine...
test1 :: TrivialABT Term '[] ('HProb ':-> 'HProb)
test1 = lam $ \x -> total (weight x)

-- | A variant of 'test1' which doesn't use 'binder' but rather
-- builds the binding structure directly.
test1b :: TrivialABT Term '[] ('HProb ':-> 'HProb)
test1b = syn (Lam_ :$ bind x (total (weight (var x))) :* End)
    where
    x = Variable (Text.pack "eks") 2 SProb


-- | Again the main thing is that this should typecheck and not
-- throw errors. We'd rather use @lam $ \x -> total x@ but that
-- causes 'binder' to throw a @<<loop>>@ exception, because 'expect'
-- needs to force variable IDs to store them in the 'Assocs'.
--
-- Should do nothing, since there's nothing we can do to a free
-- variable. Notably, should resizualise the call to 'expect'.
--
-- BUG: this version loops, but at least it throws a @<<loop>>@ error immediately.
test2 :: TrivialABT Term '[] ('HMeasure 'HProb ':-> 'HProb)
test2 = lam $ \x -> total x

-- | A variant of 'test2' which doesn't use 'binder' but rather
-- builds the binding structure directly.
test2b :: TrivialABT Term '[] ('HMeasure 'HProb ':-> 'HProb)
test2b = syn (Lam_ :$ bind x (total (var x)) :* End)
    where
    x = Variable (Text.pack "eks") 2 (SMeasure SProb)
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
    x = Variable (Text.pack "eks") 2 (SFun SInt $ SMeasure SProb)


-- | Should return the same thing as @total (dirac unit)@ (namely
-- @1@) by evaluating away the @if_ true@ part. Notably, the result
-- should not be affected by the 'weight' in the else branch.
test4 :: TrivialABT Term '[] 'HProb
test4 = total $ if_ true (dirac unit) (weight (prob_ 5) >> dirac unit)


-- | This test is similar to 'test4', but with a neutral scrutinee,
-- so the final weight should depend on what exactly @x@ happens
-- to be.
--
-- BUG: this seems to work fine for the old @Expect.hs@ but it loops
-- forever with the new @Expect2.hs@.
test5 :: TrivialABT Term '[] (HEither HUnit HUnit ':-> 'HProb)
test5 =
    lam $ \x ->
        total $
            uneither x
            (\_ -> dirac unit)
            (\_ -> weight (prob_ 5) >> dirac unit)

-- | A variant of 'test5' which doesn't use 'binder' but rather
-- builds the binding structure directly.
test5b :: TrivialABT Term '[] (HEither HUnit HUnit ':-> 'HProb)
test5b =
    syn (Lam_ :$ bind x m :* End)
    where
    x = Variable (Text.pack "eks") 2 (sEither sUnit sUnit)
    m = total $
            uneither (var x)
                (\_ -> dirac unit)
                (\_ -> weight (prob_ 5) >> dirac unit)

{-
total (array (nat_ 1) (\x -> dirac x) ! nat_ 0) :: TrivialABT Term '[] 'HProb
syn (Literal_ (VProb 1.0))
-}

-- | Regression check for the hygiene bug:
-- <https://github.com/hakaru-dev/hakaru/issues/14>
test6 :: TrivialABT Term '[] ('HMeasure (HPair 'HReal 'HReal))
test6 = constantPropagation . normalize $
    normal zero one >>= \a ->
    normal a (prob_ 2) >>= \b ->
    dirac (pair b a)

-- | This version makes sure to define 'varHint', so we can actually
-- see the problem.
test6b :: TrivialABT Term '[] ('HMeasure (HPair 'HReal 'HReal))
test6b = constantPropagation . normalize $
    syn (MBind :$ normal zero one :* bind a (
    syn (MBind :$ normal (var a) (prob_ 2) :* bind b (
    dirac (pair (var b) (var a))
    ) :* End)) :* End)
    where
    a = Variable (Text.pack "a") 0 SReal
    b = Variable (Text.pack "b") 1 SReal


-- | A second test, for hitting similar bugs even though the above works.
test7 :: [TrivialABT Term '[] ('HReal ':-> 'HMeasure 'HReal)]
test7 =
    [ constantPropagation . lam $ \d -> normalize (m' `app` d)
    | m' <- disintegrateWithVar (Text.pack "c") SReal m
    ]
    where
    a = Variable (Text.pack "a") 0 SReal
    b = Variable (Text.pack "b") 1 SReal

    m = syn (MBind :$ normal zero one :* bind a (
        syn (MBind :$ normal (var a) (prob_ 2) :* bind b (
        dirac (pair (var b) (var a))
        ) :* End)) :* End)

-- | A variant of 'test7' which doesn't use 'binder' but rather
-- builds the binding structure directly.
test7b :: [TrivialABT Term '[] ('HReal ':-> 'HMeasure 'HReal)]
test7b =
    [ constantPropagation $
        syn (Lam_ :$ bind d (normalize (m' `app` var d)) :* End)
    | m' <- disintegrateWithVar (Text.pack "c") SReal m
    ]
    where
    a = Variable (Text.pack "a") 0 SReal
    b = Variable (Text.pack "b") 1 SReal
    d = Variable (Text.pack "d") 2 SReal

    m = syn (MBind :$ normal zero one :* bind a (
        syn (MBind :$ normal (var a) (prob_ 2) :* bind b (
        dirac (pair (var b) (var a))
        ) :* End)) :* End)

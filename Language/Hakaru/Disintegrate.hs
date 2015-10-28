{-# LANGUAGE CPP
           , GADTs
           , EmptyCase
           , KindSignatures
           , DataKinds
           , PolyKinds
           , TypeOperators
           , ScopedTypeVariables
           , RankNTypes
           , MultiParamTypeClasses
           , TypeSynonymInstances
           , FlexibleInstances
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs -fno-warn-unused-binds -fno-warn-unused-imports #-}
----------------------------------------------------------------
--                                                    2015.10.26
-- |
-- Module      :  Language.Hakaru.Disintegrate
-- Copyright   :  Copyright (c) 2015 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- Disintegration via partial evaluation.
--
-- TODO: capture in the type signatures when things allow the use
-- of 'Lub' vs when they do not.
----------------------------------------------------------------
module Language.Hakaru.Disintegrate
    (
    -- * the Hakaru API
      disintegrate
    , density
    , observe
    , determine
    
    -- * Implementation details
    , Backward(..)
    , constrainValue
    , constrainOutcome
    ) where

import           Data.Number.LogFloat  (LogFloat)
#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative   (Applicative(..))
#endif

import Language.Hakaru.Syntax.IClasses
import Language.Hakaru.Syntax.Nat      (Nat)
import Language.Hakaru.Syntax.DataKind
import Language.Hakaru.Syntax.Sing
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.Datum
import Language.Hakaru.Syntax.DatumCase
import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Lazy.Types
import Language.Hakaru.Lazy
import qualified Language.Hakaru.Syntax.Prelude as P
import qualified Language.Hakaru.Expect         as E

----------------------------------------------------------------

-- BUG: get rid of the SingI requirements
-- N.B., the old version used to use the @env@ hack in order to handle the fact that free variables can change their type (eewww!!); we may need to do that again, but we should avoid it if we can possibly do so.
-- N.B., the Backward requirement is probably(?) phrased to be overly strict
-- | This function fils the role that the old @runDisintegrate@ did. It's unclear what exactly the old @disintegrate@ was supposed to be doing...
disintegrate
    :: (ABT abt, SingI a, SingI b, Backward a a)
    => abt '[] ('HMeasure (HPair a b))
    -> abt '[] (a ':-> 'HMeasure b) -- this Hakaru function is measurable
disintegrate m =
    error "TODO: disintegrate"
{-
    P.lam $ \a ->
    fromWhnf $ unM (perform m) (\ab ->
      unM (constrainValue (fst ab) a) (\h' ->
        residualizeContext h' (P.dirac $ P.snd ab)))
      emptyContext
      
-- old finally-tagless version:
    runCompose $
    P.lam $ \x ->
    runLazy $
    P.snd <$> conditionalize (P.pair (lazy . return $ Value x) P.unit) m
    -- N.B., I think that use of @unit@ is for giving a "don't care" pattern; rather than actually having anything to do with the @HUnit@ type. We should avoid this by having 'conditionalize' actually accept some form of pattern (for possible observations) rather than accepting terms.
    -- TODO: can we lift the @lam(\x ->@ over the @runCompose@? if so, then we can make sure those functions only need to be called inside 'conditionalize'
-}


-- BUG: get rid of the SingI requirements
-- N.B., the old version used to use the @env@ hack in order to handle the fact that free variables can change their type (eewww!!); we may need to do that again, but we should avoid it if we can possibly do so.
-- N.B., we intentionally phrase the Backward requirement to be overly strict
density
    :: (ABT abt, SingI a, Backward a a)
    => abt '[] ('HMeasure a)
    -> abt '[] (a ':-> 'HProb) -- TODO: make this a Haskell function?
density m =
    P.lam $ \x -> E.total (conditionalize x m)
    -- BUG: we need to wrap @x@ in the @scalar0@ wrapper before handing it to 'conditionalize'
    -- @scalar0@ means forward is no-op and backward is bot.
{-
    [ \x -> total (d `app` x)
    | d <- runCompose $
        P.lam $ \x ->
        runLazy $
        conditionalize (lazy . return $ Value x) m
    ]
=== {assuming: (`app` x) <$> runCompose f == runCompose (f `app` x) }
    P.lam $ \x ->
    total $
    runCompose $
    runLazy $
    conditionalize (lazy . return $ Value x) m
-}


-- BUG: get rid of the SingI requirements
-- N.B., the old version used to use the @env@ hack (but not on the first argument) in order to handle the fact that free variables can change their type (eewww!!); we may need to do that again, but we should avoid it if we can possibly do so.
-- TODO: what's the point of having this function instead of just using @disintegrate m `app` x@ ? I.E., what does the @scalar0@ wrapper actually achieve; i.e., how does it direct things instead of just failing when we try to go the wrong direction?
-- BUG: come up with new names avoid name conflict vs the Prelude function.
observe
    :: (ABT abt, SingI a, SingI b, Backward a a)
    => abt '[] a
    -> abt '[] ('HMeasure (HPair a b))
    -> abt '[] ('HMeasure b)
observe x m =
    {- runCompose $ -}
    {- runLazy $ -}
    P.snd P.<$> conditionalize (P.pair x P.unit) m
    -- TODO: can we lift the @(snd <$>)@ over the @runCompose@ and @runLazy@ functions? if so, then we can make sure those functions only need to be called inside 'conditionalize'
    -- N.B., see the note at 'disintegrate' about the use of @unit@ here...


-- N.B., all arguments used to have type @Lazy s repr@ instead of @abt '[]@
-- | This is what used to be called @disintegrate@. I think this new name captures whatever it is that funtion was actually supposed to be doing?
--
-- The first argument is a representation of a projection function followed by equality; for example @(pair x unit)@ rather than @(x ==) . fst@. This trick isn't used in the paper, and probably doesn't generalize...
--
-- TODO: whatever this function is supposed to do, it should probably be the one that's the primop rather than 'disintegrate'.
conditionalize
    :: (ABT abt, Backward ab a)
    => abt '[] a
    -> abt '[] ('HMeasure ab)
    -> abt '[] ('HMeasure ab)
conditionalize a m =
    error "TODO: conditionalize"
    {-
    let n = do
            x  <- forward m
            ab <- memo (unMeasure x)
            backward_ ab a
            return ab
    in Lazy (return . Measure $ Lazy (n >>= forward) (\t -> n >>= (`backward` t))) (\_ -> M $ \_ _ -> bot)
    -}


-- | Eliminate uses of 'Lub_' by chosing one of the alternatives
-- arbitrarily. In the future, this function should be replaced by
-- a better one that takes some sort of strategy for deciding which
-- alternative to choose.
--
-- HACK: it's unclear (to me) whether this is actually the same as
-- the function of the same name in "Language.Hakaru.Lazy".
--
-- TODO: should we return @Maybe (abt '[] a)@ or should we allow @bot@ at the very top level of the result?
determine :: (ABT abt) => abt '[] a -> abt '[] a
determine m = error "TODO: determine"


----------------------------------------------------------------
----------------------------------------------------------------
-- BUG: replace all the -XTypeSynonymInstances with a single general instance for all @'HData@

class Backward (b :: Hakaru) (a :: Hakaru) where
    {-
    backward_ :: (ABT abt) => Lazy s abt b -> Lazy s abt a -> M s abt ()
    -}

instance Backward a HUnit where
    {-
    backward_ _ _ = return ()
    -}

instance Backward HBool HBool where
    {-
    backward_ a x =
        ifM (equal_ a x) >>= \b -> if b then return () else P.reject
    -}

instance Backward 'HInt 'HInt where
    {-
    backward_ a x = forward x >>= backward a
    -}

instance Backward 'HReal 'HReal where
    {-
    backward_ a x = forward x >>= backward a
    -}

instance Backward 'HProb 'HProb where
    {-
    backward_ a x = forward x >>= backward a
    -}

instance (Backward a x, Backward b y)
    => Backward (HPair a b) (HPair x y)
    where
    {-
    backward_ ab xy = do
        (a,b) <- unpairM ab
        (x,y) <- unpairM xy
        backward_ a x
        backward_ b y
    -}

instance (Backward a x, Backward b y)
    => Backward (HEither a b) (HEither x y)
    where
    {-
    backward_ ab xy = do
        a_b <- uneitherM ab
        x_y <- uneitherM xy
        case (a_b, x_y) of
            (Left  a, Left  x) -> backward_ a x
            (Right b, Right y) -> backward_ b y
            _                  -> P.reject
    -}

----------------------------------------------------------------
----------------------------------------------------------------
{-
data L s abt a = L
    { forward  :: M s abt (Whnf (L s abt) a)
    , backward :: Whnf (L s abt) a -> M s abt ()
    }

-- TODO: make the length indexing explicit:
-- > data C abt a = C { unC :: forall n. Sing n -> [Vec (Some1 abt) n -> a] }
--
-- TODO: does the old version actually mean to erase type info? or should we rather use:
-- > data C abt a = C { unC :: forall xs. Sing xs -> [List1 abt xs -> a] }
--
-- TODO: should we add back in something like @C@ for interpreting\/erasing the uses of 'Lub_'?
data C abt a = C { unC :: Nat -> [[Some1 abt] -> a] }

type Lazy s abt a = L s (C abt) a
-}

----------------------------------------------------------------
----------------------------------------------------------------
-- TODO: see the todo for 'constrainOutcome'
constrainValue :: (ABT abt) => abt '[] a -> Whnf abt a -> M abt ()
constrainValue = error "TODO: constrainValue"
{-
constrainValue e0 v0 =
    case e0 of
    u | atomic u -> M $ \c h -> P.bot
    Real _       -> M $ \c h -> P.bot
    Fst e1 | not (atomic e1) -> evaluate e1 >>= ((`constrainValue` v0) . fst)
    Snd e1 | not (atomic e1) -> evaluate e1 >>= ((`constrainValue` v0) . snd)
    Negate e1 -> constrainValue e1 (negate v0)
    Recip e1 -> M $ \c h -> P.weight (P.recip (v0 P.^ P.nat_ 2)) P.>> unM (constrainValue e1 (recip v0)) c h
    Plus e1 e2 -> M $ \c h ->
        unM (evaluate e1) (\v1 -> unM (constrainValue e2 (v0 - v1)) c) h
        `P.lub`
        unM (evaluate e2) (\v2 -> unM (constrainValue e1 (v0 - v2)) c) h
    Times e1 e2 -> M $ \c h ->
        unM (evaluate e1) (\v1 -> abs v1 (\v1' h' -> P.weight (P.recip v1') P.>> unM (constrainValue e2 (v0 / v1)) c h')) h
        `P.lub`
        unM (evaluate e2) (\v2 -> abs v2 (\v2' h' -> P.weight (P.recip v2') P.>> unM (constrainValue e1 (v0 / v2)) c h')) h
    Var x ->  M $ \c h ->
        case lookup x h of
        Missing -> error "constrainValue: variable is missing in heap!"
        Found h1 binding h2 ->
            case binding of
            SBind _x e1 ->
                unM (constrainOutcome e1 v0) (\h1' -> c (glue h1' (SLet x v0) h2)) h1
            SLeft _x e1 ->
                -- TODO: figure out how to reuse the implementation of @unleft@\/@unright@ from 'update'
                unM (evaluate e1) (\v1 -> unleft v1 (\e2 -> unM (constrainValue e1 v0) (\h1' -> c (glue h1' (SLet x v0) h2)))) h1
            SRight _x e1 ->
                unM (evaluate e1) (\v1 -> unright v1 (\e2 -> unM (constrainValue e1 v0) (\h1' -> c (glue h1' (SLet x v0) h2)))) h1
-}

-- TODO: do we really need to allow all Whnf, or do we just need
-- variables (or neutral terms)? Do we actually want (hnf)terms at
-- all, or do we want (hnf)patterns or something to more generally
-- capture (hnf)measurable events?
constrainOutcome
    :: (ABT abt) => abt '[] ('HMeasure a) -> Whnf abt a -> M abt ()
constrainOutcome = error "TODO: constrainOutcome"
{-
constrainOutcome e0 v =
    case e0 of
    u | atomic u    -> M $ \c h -> P.bot
    Lebesgue        -> M $ \c h -> c h
    Uniform lo hi   -> M $ \c h -> P.observe (lo P.<= v P.&& v P.<= hi) P.>> P.weight (P.recip (hi P.- lo)) P.>> c h
    Return e        -> constrainValue e v
    MBind g (bind x e) -> push (SBind x g) >> constrainOutcome e v
    Superpose es    -> P.superpose <$> T.traverse (`constrainOutcome` v) es -- TODO: not quite right; need to push the SWeight in each branch
    e | not (hnf e) -> (`constrainOutcome` v) =<< evaluate e


unleft :: Whnf abt (HEither a b) -> M abt (abt '[] a)
unleft (Left  e) = M $ \c h -> c e h
unleft (Right e) = M $ \c h -> P.reject
unleft u         = M $ \c h -> P.uneither u (\x -> c x h) (\_ -> P.reject)

unright :: Whnf abt (HEither a b) -> M abt (abt '[] a)
unright (Right e) = M $ \c h -> c e h
unright (Left  e) = M $ \c h -> P.reject
unright u         = M $ \c h -> P.uneither u (\_ -> P.reject) (\x -> c x h)
-}

----------------------------------------------------------------
----------------------------------------------------------- fin.

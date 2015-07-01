{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts, FlexibleInstances,
    TypeFamilies, StandaloneDeriving, GeneralizedNewtypeDeriving, GADTs,
    RankNTypes, ScopedTypeVariables, UndecidableInstances, TypeOperators, DataKinds, InstanceSigs #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2015.06.30
-- |
-- Module      :  Language.Hakaru.Syntax.Expect
-- Copyright   :  Copyright (c) 2015 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- This is a fork of "Language.Hakaru.Expect" to work with our new
-- AST. This module shouldn't actually be called
-- "Language.Hakaru.Syntax.Expect"; it should keep the old name,
-- once we switch everything over to using the new AST.
----------------------------------------------------------------
module Language.Hakaru.Syntax.Expect
    ( Expect(..)
    , Expect'
    , total
    , normalize
    ) where

import Language.Hakaru.Syntax.DataKind
import Language.Hakaru.Syntax.TypeEq
import Language.Hakaru.Syntax.AST
    (Hakaru(..), HakaruFun(..),
       Order(..), Base(..), Mochastic(..), Integrate(..), Lambda(..),
       fst_, snd_, summateV, mapWithIndex)

----------------------------------------------------------------
-- | A newtype wraper for packaging up the 'Expect'' type family,
-- so we can provide instances on it, etc.
newtype Expect (abt :: Hakaru -> *) (a :: Hakaru) =
    Expect { unExpect :: abt (Expect' a) }

type family   Expect' (a :: Hakaru) :: Hakaru
-- This type family must be changed in lockstep with typeExpect below
type instance Expect' 'HNat          = 'HNat
type instance Expect' 'HInt          = 'HInt 
type instance Expect' 'HProb         = 'HProb 
type instance Expect' 'HReal         = 'HReal 
type instance Expect' ('HMeasure a)  =
    HPair ('HMeasure (Expect' a)) ('HFun ('HFun (Expect' a) 'HProb) 'HProb)
    -- TODO: what we really want are Haskell types here:
    -- > (abt 'HMeasure (Expect' a), ((anb (Expect' a) -> abt 'HProb) -> abt 'HProb)
    -- That's necesary to get rid of the administrative redexes.
    --
    -- TODO: ultimately, we'd like to be able to specify an explicit measure to take the expectiation of, leaving the rest alone.
type instance Expect' ('HArray a)    = 'HArray  (Expect' a)
type instance Expect' ('HFun a b)    = 'HFun (Expect' a) (Expect' b)
type instance Expect' ('HData t xss) = 'HData (ExpectCon t) (ExpectCode xss)

type family   ExpectCon (x :: HakaruCon Hakaru) :: HakaruCon Hakaru 
type instance ExpectCon ('HCon s)    = 'HCon s
type instance ExpectCon (c ':@ a)    = ExpectCon c ':@ Expect' a

type family   ExpectCode (a :: [[HakaruFun]]) :: [[HakaruFun]]
type instance ExpectCode '[]         = '[] 
type instance ExpectCode (x ': xs)   = ExpectProd x ': ExpectCode xs

type family   ExpectProd (a :: [HakaruFun]) :: [HakaruFun]
type instance ExpectProd '[]         = '[] 
type instance ExpectProd (x ': xs)   = (ExpectFun x ': ExpectProd xs)

type family   ExpectFun (x :: HakaruFun) :: HakaruFun 
type instance ExpectFun 'I           = I 
type instance ExpectFun ('K x)       = 'K (Expect' x)


-- TODO: it'd be better to store type-signature singletons at each
-- ABT node, then use 'jmEq' to decide @TypeEq a (Expect' a)@, and
-- do case analysis on the 'Refl' to simply rewrite the types of
-- subterms without needing to traverse them. Using 'jmEq' means
-- we'd have to traverse the /type/ in order to generate the 'Refl'
-- proof, but types are generally much smaller than terms. In order
-- to minimize the memory overhead of keeping track of these
-- singletons, we should use hash-consing and just store the hash
-- at each node; the store of singletons would need to be passed
-- along as some sort of general environment around the ABT. Heck,
-- we could even just store (hashes of) the 'TypeEq' proofs themselves!
--
-- TODO: is there any way that when 'jmEq' fails, we could get some
-- kind of certificate that says where it failed, which we could
-- then use to traverse a large chunk of the term before trying
-- again? (rather than repeating the failing check at each ABT
-- node).

-- But for now, extremely slow implementation: We still have to
-- traverse the 'Value', 'NaryOp', etc constructors to generate the
-- proof; but the casting should emable us to return the same object
-- in memory, rather than reallocating it.

expectRefl_Value :: Value a -> TypeEq a (Expect' a)
expectRefl_Value (Bool_ _) = Refl
expectRefl_Value (Nat_  _) = Refl
expectRefl_Value (Int_  _) = Refl
expectRefl_Value (Prob_ _) = Refl
expectRefl_Value (Real_ _) = Refl

expectRefl_NaryOp :: NaryOp a -> TypeEq a (Expect' a)
expectRefl_NaryOp And  = Refl
expectRefl_NaryOp Or   = Refl
expectRefl_NaryOp Xor  = Refl
expectRefl_NaryOp Iff  = Refl
expectRefl_NaryOp Min  = Refl
expectRefl_NaryOp Max  = Refl
expectRefl_NaryOp Sum  = Refl
expectRefl_NaryOp Prod = Refl

expectRefl_PrimOp :: PrimOp a -> TypeEq a (Expect' a)
expectRefl_PrimOp Not         = Refl
expectRefl_PrimOp Impl        = Refl
expectRefl_PrimOp Diff        = Refl
expectRefl_PrimOp Nand        = Refl
expectRefl_PrimOp Nor         = Refl
expectRefl_PrimOp Pi          = Refl
expectRefl_PrimOp Sin         = Refl
expectRefl_PrimOp Cos         = Refl
expectRefl_PrimOp Tan         = Refl
expectRefl_PrimOp Asin        = Refl
expectRefl_PrimOp Acos        = Refl
expectRefl_PrimOp Atan        = Refl
expectRefl_PrimOp Sinh        = Refl
expectRefl_PrimOp Cosh        = Refl
expectRefl_PrimOp Tanh        = Refl
expectRefl_PrimOp Asinh       = Refl
expectRefl_PrimOp Acosh       = Refl
expectRefl_PrimOp Atanh       = Refl
expectRefl_PrimOp RealPow     = Refl
expectRefl_PrimOp Exp         = Refl
expectRefl_PrimOp Log         = Refl
expectRefl_PrimOp Infinity    = Refl
expectRefl_PrimOp NegativeInfinity = Refl
expectRefl_PrimOp GammaFunc   = Refl
expectRefl_PrimOp BetaFunc    = Refl
{- -- BUG: these need to have some singleton for their polymorphism, so we can match on that to exclude HMeasure
expectRefl_PrimOp Empty     = o
expectRefl_PrimOp Index     = o
expectRefl_PrimOp Size      = o
expectRefl_PrimOp Reduce    = o

-- These ones will have singletons anyways, for their class constraints
-- These look to be translated as themseves, given the Eq, Ord, Num, Fractional, Floating instances on Expect
expectRefl_PrimOp Less        = Refl
expectRefl_PrimOp Equal       = Refl
expectRefl_PrimOp NatPow      = Refl
expectRefl_PrimOp Negate      = Refl
expectRefl_PrimOp Abs         = Refl
expectRefl_PrimOp Signum      = Refl
expectRefl_PrimOp Recip       = Refl
expectRefl_PrimOp NatRoot     = Refl
expectRefl_PrimOp Erf         = Refl
-}
expectRefl_PrimOp _ = error "expectPrimOp: TODO"


-- BUG: this is identical (control-flow wise) to 'fmap1'; but we can't use 'fmap1' because 'expect' isn't natural! We're gonna want to weaken the definition so that we can apply any given type function to the index (where the current 'fmap1' just uses the identity function). We'll have to use newtypes in order to pass the proxies to know which type function it is.
expectDatum
    :: (forall b. f b -> g (Expect' b))
    -> Datum f a
    -> Datum g (Expect' a)
expectDatum f (Datum d) = Datum (expectPartialDatum f d)

expectPartialDatum
    :: (forall b. f b -> g (Expect' b))
    -> PartialDatum f a
    -> PartialDatum g (Expect' a)
expectPartialDatum f = go
    where
    go Nil           = Nil
    go (Cons  d1 d2) = Cons  (go d1) (go d2)
    go (Zero  d)     = Zero  (go d)
    go (Succ  d)     = Succ  (go d)
    go (Konst e)     = Konst (f e)
    go (Ident e)     = Ident (f e)


-- There are no patterns on 'HMeasure'. At best, we can use a trivial
-- pattern to capture\/discard an 'HMeasure' subcomponent of some
-- data type. Alas, we can't make 'Pattern' into a functor, since
-- it has the wrong kind;
-- TODO: Define a new polykinded Functor class?
expectPattern :: Pattern a -> Pattern (Expect' a)
expectPattern PWild      = PWild
expectPattern PVar       = PVar
expectPattern (PDatum d) = PDatum (expectDatum expectPattern d)


expectBranch
    :: (ABT abt)
    => Branch a abt b
    -> Branch (Expect' a) abt (Expect' b)
expectBranch (Branch pat body) =
    Branch (expectPattern pat) (expect body)

expectSing :: Sing a -> Sing (Expect' a)
expectSing SNat         = SNat
expectSing SInt         = SInt
expectSing SProb        = SProb
expectSing SReal        = SReal
expectSing (SArray a)   = SArray (expectSing a)
expectSing (SFun a b)   = SFun (expectSing a) (expectSing b)
expectSing (SMeasure a) =
    let xa = expectSing a
    in SPair (SMeasure xa) (SFun (SFun xa SProb) SProb)
expectSing (SData con code) =
    SData (expectSing_Con con) (expectSing_Code code)
    where
    expectSing_Con (SCon s)   = SCon s
    expectSing_Con (SApp f a) = SApp (expectSing_Con f) (expectSing a)
    
    expectSing_Code SVoid        = SVoid
    expectSing_Code (SPlus x xs) =
        SPlus (expectSing_Prod x) (expectSing_Code xs)
        
    expectSing_Prod SNil         = SNil
    expectSing_Prod (SCons x xs) =
        SCons (expectSing_Fun x) (expectSing_Prod xs)
    
    expectSing_Fun SIdent     = SIdent
    expectSing_Fun (SKonst a) = SKonst (expectSing a)

    
expectAST :: AST ast a -> AST ast (Expect' a)
expectAST (Lam_        p  e)     = Lam_ Proxy       (expect e)
expectAST (App_        e1 e2)    = App_ (expect e1) (expect e2)
expectAST (Let_        e1 e2)    = Let_ (expect e1) (expect e2)
expectAST (Fix_        e)        = Fix_ (expect e)
expectAST (Ann_        p  e)     = Ann_ (expectSing p) (expect e)
expectAST t@(PrimOp_     o)      = case expectRefl_NaryOp o of Refl -> t
expectAST t@(NaryOp_     o  _)   = case expectRefl_NaryOp o of Refl -> t
expectAST t@(Integrate_  e1 e2 e3) = t
expectAST t@(Summate_    e1 e2 e3) = t
expectAST t@(Value_      v)      = case expectRefl_Value v of Refl -> t
expectAST (CoerceTo_   c  e)     = CoerceTo_   c      (expect e)
expectAST (UnsafeFrom_ c  e)     = UnsafeFrom_ c      (expect e)
expectAST (Array_      e1 e2)    = Array_ (expect e1) (expect e2)
expectAST (Datum_      d)        = Datum_ (expectDatum expect d)
expectAST (Case_       e bs)     = Case_  (expect e)  (map expectBranch bs)
{-
  unpair (Expect ab) k =
    Expect (unpair ab (\a b -> unExpect (k (Expect a) (Expect b))))
  uneither (Expect ab) ka kb =
    Expect $ uneither ab (unExpect . ka . Expect) (unExpect . kb . Expect)
  if_ (Expect eb) (Expect et) (Expect ef) = Expect $ if_ eb et ef
-}

expectAST (Measure_    o)        = ...
expectAST (Bind_       e1 e2)    = Bind_       (f e1) (f e2)
expectAST (Superpose_  pes)      = Superpose_  (map (f *** f) pes)
expectAST (Dp_         e1 e2)    = Dp_         (f e1) (f e2)
expectAST (Plate_      e)        = Plate_      (f e)
expectAST (Chain_      e)        = Chain_      (f e)
expectAST (Lub_        e1 e2)    = Lub_        (f e1) (f e2)
expectAST Bot_                   = Bot_



expect :: ABT abt => abt a -> abt (Expect' a)


instance (Integrate repr) => Integrate (Expect repr) where
  integrate (Expect lo) (Expect hi) f =
    Expect (integrate lo hi (unExpect . f . Expect))
  summate (Expect lo) (Expect hi) f =
    Expect (summate lo hi (unExpect . f . Expect))

reflectPair :: (Lambda repr) =>
               (a -> (a -> repr w) -> repr w) ->
               (b -> (b -> repr w) -> repr w) ->
               (a,b) -> ((a,b) -> repr w) -> repr w
reflectPair ra rb (a,b) c = ra a (\a' -> rb b (\b' -> c (a',b')))

reflectList :: (Lambda repr) =>
               (a -> (a -> repr w) -> repr w) ->
               [a] -> ([a] -> repr w) -> repr w
reflectList _  []     c = c []
reflectList ra (a:as) c = ra a (\a' -> reflectList ra as (\as' -> c (a':as')))

reflect :: (Lambda repr) =>
           [(Expect repr a, Expect repr b)] ->
           ([(repr (Expect' a), repr (Expect' b))] -> repr w) -> repr w
reflect ab_s = reflectList (reflectPair let_ let_)
                 [ (a,b) | (Expect a, Expect b) <- ab_s ]

instance (Mochastic repr, Integrate repr, Lambda repr)
      => Mochastic (Expect repr) where
  dirac (Expect a) = Expect $ let_ a $ \a' -> pair
    (dirac a')
    (lam (\c -> c `app` a'))
  bind (Expect m) k =
    Expect $ let_ (lam (unExpect . k . Expect)) $ \k' ->
             unpair m $ \m1 m2 ->
             pair (bind m1 (fst_ . app k'))
                  (lam (\c -> m2 `app` lam (\a -> snd_ (app k' a) `app` c)))
  lebesgue = Expect $ pair
    lebesgue
    (lam (integrate negativeInfinity infinity . app))
  counting = Expect $ pair
    counting
    (lam (summate   negativeInfinity infinity . app))
  superpose pms = Expect $ reflect pms $ \pms' -> pair
    (superpose [ (p, fst_ m) | (p, m) <- pms' ])
    (lam (\c -> sum [ p * app (snd_ m) c | (p, m) <- pms' ]))
  uniform (Expect lo) (Expect hi) = Expect $ pair
    (uniform lo hi)
    (lam (\f -> integrate lo hi (\x -> app f x / unsafeProb (hi - lo))))
  normal (Expect mu) (Expect sd) = Expect $ pair
    (normal mu sd)
    (lam (\c -> integrate negativeInfinity infinity (\x ->
     exp_ (- (x - mu)^(2::Int) / fromProb (2 * pow_ sd 2))
     / sd / sqrt_ (2 * pi_) * app c x)))
  categorical (Expect ps) = Expect $ pair
    (categorical ps)
    (lam (\c -> let_ (summateV ps) $ \tot ->
                if_ (less 0 tot)
                    (summateV (mapWithIndex (\i p -> p * app c i) ps) / tot)
                    0))
  poisson (Expect l) = Expect $ pair
    (poisson l)
    (lam (\c -> flip (if_ (less 0 l)) 0 (summate 0 infinity (\x ->
     pow_ l (fromInt x) / gammaFunc (fromInt x + 1) / exp_ (fromProb l)
     * app c x))))
  gamma (Expect shape) (Expect scale) = Expect $ pair
    (gamma shape scale)
    (lam (\c -> integrate 0 infinity (\x ->
     let x_ = unsafeProb x
         shape_ = fromProb shape in
     (pow_ x_ (fromProb (shape - 1)) * exp_ (- fromProb (x_ / scale))
      / (pow_ scale shape_ * gammaFunc shape_) * app c (unsafeProb x)))))
  beta (Expect a) (Expect b) = Expect $ pair
    (beta a b)
    (lam (\c -> integrate 0 1 (\x -> pow_ (unsafeProb x    ) (fromProb a - 1)
                                   * pow_ (unsafeProb (1-x)) (fromProb b - 1)
                                   / betaFunc a b * app c (unsafeProb x))))


total :: (Lambda repr, Base repr) => Expect repr ('HMeasure a) -> repr 'HProb
total (Expect m) = unpair m (\_ m2 -> m2 `app` lam (\_ -> 1))

normalize
    :: (Integrate repr, Lambda repr, Mochastic repr)
    => Expect repr ('HMeasure a) -> repr ('HMeasure (Expect' a))
normalize (Expect m) = unpair m (\m1 m2 ->
  superpose [(recip (m2 `app` lam (\_ -> 1)), m1)])

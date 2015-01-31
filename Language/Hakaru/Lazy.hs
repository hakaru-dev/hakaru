{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts, FlexibleInstances, Rank2Types, GADTs, TypeFamilies, LambdaCase #-}
{-# OPTIONS -Wall #-}

module Language.Hakaru.Lazy where

import Prelude hiding (Real)
import Language.Hakaru.Syntax (Real, Prob, Measure, Number, EqType(Refl),
       Order(..), Base(..), Mochastic(..), Integrate(..), Lambda(..),
       weight)
import Control.Monad (liftM2, forM)
import Data.Monoid (Monoid (mempty, mappend, mconcat))
import Data.Function (on)
import Data.Either (partitionEithers)
import Unsafe.Coerce (unsafeCoerce)

unpair' :: (Base repr) =>
           repr (a,b) -> ((repr a, repr b) -> repr c) -> repr c
unpair' ab c = unpair ab (curry c)

uneither' :: (Base repr) =>
             repr (Either a b) -> (Either (repr a) (repr b) -> repr c) -> repr c
uneither' ab c = uneither ab (c . Left) (c . Right)

newtype M s repr a = M { unM :: forall w. (Monoid (repr (Measure w))) =>
  (a -> Heap s repr -> repr (Measure w)) -> Heap s repr -> repr (Measure w) }

instance Monad (M s repr) where
  return a = M (\c -> c a)
  m >>= k  = M (\c -> unM m (\a -> unM (k a) c))

instance Functor (M s repr) where fmap f m = m >>= return . f

instance Monoid (M s repr a) where
  mempty                = M (\_ _ -> mempty)
  mappend (M m1) (M m2) = M (\c h -> mappend (m1 c h) (m2 c h))
  mconcat ms            = M (\c h -> mconcat (map (\(M m) -> m c h) ms))

reject :: (Mochastic repr) => M s repr a
reject = M (\_ _ -> superpose [])

insert :: (forall w. (a -> repr (Measure w)) -> repr (Measure w)) -> M s repr a
insert f = M (\c h -> f (\a -> c a h))

insert_ :: (forall w. repr (Measure w) -> repr (Measure w)) -> M s repr ()
insert_ f = insert (\m -> f (m ()))

lift :: (Mochastic repr) => repr (Measure a) -> M s repr (repr a)
lift m = insert (bind m)

cond :: (Mochastic repr) => repr Bool -> repr (Measure w) -> repr (Measure w)
cond b m = if_ b m (superpose [])

data Lazy s (repr :: * -> *) a = Lazy
  { forward  :: M s repr (Whnf s repr a)
  , backward :: {- Number a => -} repr a -> M s repr () }

lazy :: M s repr (Whnf s repr a) -> Lazy s repr a
lazy m = Lazy m (const mempty)

bidirectional :: (Number a) =>
                 M s repr (Whnf s repr a) ->
                 (repr a -> M s repr ()) ->
                 Lazy s repr a
bidirectional = Lazy

-- TODO: Whnf,Binding,Retrieval for lists and vectors
data Whnf s (repr :: * -> *) a where
  Pair    :: Lazy s repr a -> Lazy s repr b -> Whnf s repr (a,b)
  Inl     :: Lazy s repr a ->                  Whnf s repr (Either a b)
  Inr     :: Lazy s repr b ->                  Whnf s repr (Either a b)
  Value   :: repr a ->                         Whnf s repr a
  Measure :: Lazy s repr a ->                  Whnf s repr (Measure a)

unValue :: Whnf s repr a -> repr a
-- only safe for scalar types, i.e., types that are not of any of the forms
-- (a,b), (Either a b), (Measure a), [a], (Vector a)
unValue (Value a) = a

data Heap s repr = Heap
  { fresh :: Int
  , bound :: [Binding s repr] }

newtype Loc s a = Loc Int
  deriving (Show)

jmEq :: Loc s a -> Loc s b -> Maybe (EqType a b)
jmEq (Loc a) (Loc b) | a == b    = Just (unsafeCoerce Refl)
                     | otherwise = Nothing

gensym :: M s repr (Loc s a)
gensym = M (\c h@Heap{fresh=f} -> c (Loc f) h{fresh = succ f})

data Binding s repr where
  Bind    :: Loc s a ->            Lazy s repr a            -> Binding s repr
  Unpair  :: Loc s a -> Loc s b -> Lazy s repr (a,b)        -> Binding s repr
  Uninl   :: Loc s a ->            Lazy s repr (Either a b) -> Binding s repr
  Uninr   :: Loc s b ->            Lazy s repr (Either a b) -> Binding s repr
  Iftrue  ::                       Lazy s repr Bool         -> Binding s repr
  Iffalse ::                       Lazy s repr Bool         -> Binding s repr

store :: Binding s repr -> M s repr ()
store entry = M (\c h@Heap{bound=b} -> c () h{bound = entry : b})

update :: Loc s a -> Whnf s repr a -> M s repr ()
update l result = store (Bind l (lazy (return result)))

finally :: (Monad m) => (a -> m ()) -> a -> m a
finally k a = k a >> return a

memo :: (Mochastic repr) => Lazy s repr a -> M s repr (Lazy s repr a)
memo m = do l <- gensym
            store (Bind l m)
            return (Lazy (fwdLoc l) (bwdLoc l))

data Retrieval s repr a where
  RBind  :: Lazy s repr a ->                Retrieval s repr a
  RFst   :: Loc s b -> Lazy s repr (a,b) -> Retrieval s repr a
  RSnd   :: Loc s a -> Lazy s repr (a,b) -> Retrieval s repr b
  RInl   :: Lazy s repr (Either a b) ->     Retrieval s repr a
  RInr   :: Lazy s repr (Either a b) ->     Retrieval s repr b

locate :: Loc s a -> Binding s repr -> Maybe (Retrieval s repr a)
locate l (Bind   l1    rhs) = fmap (\Refl -> RBind rhs) (jmEq l l1)
locate l (Unpair l1 l2 rhs) = case (fmap (\Refl -> RFst l2 rhs) (jmEq l l1),
                                    fmap (\Refl -> RSnd l1 rhs) (jmEq l l2))
                              of (Just _ , Just _ ) -> err
                                 (Just r , Nothing) -> Just r
                                 (Nothing, Just r ) -> Just r
                                 (Nothing, Nothing) -> Nothing
  where err = error ("Duplicate variable " ++ show l)
locate l (Uninl  l1    rhs) = fmap (\Refl -> RInl rhs) (jmEq l l1)
locate l (Uninr  l2    rhs) = fmap (\Refl -> RInr rhs) (jmEq l l2)
locate _ (Iftrue       _  ) = Nothing
locate _ (Iffalse      _  ) = Nothing

retrieve :: Loc s a -> M s repr (Retrieval s repr a)
retrieve l = M (\c h ->
  case partitionEithers [ case locate l entry of Just r -> Right r
                                                 Nothing -> Left entry
                        | entry <- bound h ] of
    (_   , []   ) -> error ("Unbound location " ++ show l)
    (left, [r]  ) -> c r h{bound=left}
    (_   , _:_:_) -> error ("Duplicate heap entry " ++ show l))

fwdLoc :: (Mochastic repr) => Loc s a -> M s repr (Whnf s repr a)
fwdLoc l = retrieve l >>= \case
  RBind rhs -> forward rhs >>= finally (update l)
  RFst l2 rhs -> forward rhs >>= \case
    Pair a b -> do store (Bind l2 b)
                   forward a >>= finally (update l)
    Value ab -> do (a, b) <- insert (unpair' ab)
                   update l2 (Value b)
                   finally (update l) (Value a)
  RInl rhs -> forward rhs >>= \case
    Inl rhs  -> forward rhs >>= finally (update l)
    Inr _    -> reject
    Value ab -> insert (uneither' ab) >>= \case
                  Left  a -> finally (update l) (Value a)
                  Right _ -> reject

bwdLoc :: (Mochastic repr) => Loc s a -> repr a -> M s repr ()
bwdLoc l t = retrieve l >>= \case
  RBind rhs -> backward rhs t >> update l (Value t)
  RFst l2 rhs -> forward rhs >>= \case
    Pair a b -> do store (Bind l2 b)
                   backward a t >> update l (Value t)
    Value _ -> mempty
  RInl rhs -> forward rhs >>= \case
    Inl rhs -> backward rhs t >> update l (Value t)
    Inr _   -> reject
    Value _ -> mempty

scalar0 :: repr a -> Lazy s repr a
scalar0 op = lazy (return (Value op))

scalar1 :: (repr a -> repr b) -> Lazy s repr a -> Lazy s repr b
scalar1 op a = lazy (do Value a <- forward a
                        return (Value (op a)))

scalar2 :: (repr a -> repr b -> repr c) ->
           Lazy s repr a -> Lazy s repr b -> Lazy s repr c
scalar2 op a b = lazy (do Value a <- forward a
                          Value b <- forward b
                          return (Value (op a b)))

instance (Order repr Int) => Order (Lazy s repr) Int where
  less  = scalar2 less
  equal = scalar2 equal

instance (Order repr Real) => Order (Lazy s repr) Real where
  less  = scalar2 less
  equal = scalar2 equal

instance (Order repr Prob) => Order (Lazy s repr) Prob where
  less  = scalar2 less
  equal = scalar2 equal

add :: (Num (repr a), Number a) =>
       Lazy s repr a -> Lazy s repr a -> Lazy s repr a
add x y = bidirectional
  ((liftM2 ((Value.) . (+) `on` unValue) `on` forward) x y)
  (\t -> mappend (forward x >>= \(Value r) -> backward y (t - r))
                 (forward y >>= \(Value r) -> backward x (t - r)))

neg :: (Num (repr a), Number a) =>
       Lazy s repr a -> Lazy s repr a
neg x = bidirectional
  (fmap (Value . negate . unValue) (forward x))
  (\t -> backward x (negate t))

instance (Num (repr Int)) => Num (Lazy s repr Int) where
  (+) = add
  negate = neg
  fromInteger x = bidirectional (return (Value (fromInteger x)))
                                (const (return ()))

instance (Num (repr Real)) => Num (Lazy s repr Real) where
  (+) = add
  negate = neg
  fromInteger x = scalar0 (fromInteger x)

instance (Num (repr Prob)) => Num (Lazy s repr Prob) where
  (+) = add
  negate = neg
  fromInteger x = scalar0 (fromInteger x)

instance (Mochastic repr) => Fractional (Lazy s repr Real) where
  recip x = bidirectional
    (fmap (Value . recip . unValue) (forward x))
    (\t -> do insert_ (weight (recip (unsafeProb (t * t))))
              backward x (recip t))

instance (Mochastic repr) => Fractional (Lazy s repr Prob) where
  recip x = bidirectional
    (fmap (Value . recip . unValue) (forward x))
    (\t -> do insert_ (weight (recip (t * t)))
              backward x (recip t))

instance (Mochastic repr) => Floating (Lazy s repr Real) where
  exp x = bidirectional
    (fmap (Value . exp . unValue) (forward x))
    (\t -> do insert_ (cond (less 0 t) . weight (recip (unsafeProb t)))
              backward x (log t))

instance (Mochastic repr) => Base (Lazy s repr) where
  gammaFunc = scalar1 gammaFunc
  betaFunc  = scalar2 betaFunc

measure :: Lazy s repr a -> Lazy s repr (Measure a)
measure = lazy . return . Measure

unMeasure :: (Mochastic repr) => Whnf s repr (Measure a) -> Lazy s repr a
unMeasure (Measure m) = m
unMeasure (Value m) = lazy (fmap Value (lift m))

instance (Mochastic repr) => Mochastic (Lazy s repr) where
  dirac x  = measure $ x
  bind m k = measure $ Lazy
    (forward m >>= memo . unMeasure >>= \a ->
     forward (k a) >>= \ka -> forward (unMeasure ka))
    (\t -> forward m >>= memo . unMeasure >>= \a ->
           forward (k a) >>= \ka -> backward (unMeasure ka) t)
  lebesgue = measure $ bidirectional (fmap Value (lift lebesgue))
                                     (const (return ()))
  counting = measure $ bidirectional (fmap Value (lift counting))
                                     (const (return ()))
  superpose pms = lazy $ do
    pms <- forM pms (\(p,m) -> liftM2 (,) (fmap unValue   (forward p))
                                          (fmap unMeasure (forward m)))
    return (Measure (Lazy
      (      M (\c h -> superpose [ (p, unM (forward  m  ) c h) | (p,m) <- pms ]))
      (\t -> M (\c h -> superpose [ (p, unM (backward m t) c h) | (p,m) <- pms ]))))

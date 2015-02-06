{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts, FlexibleInstances,
             Rank2Types, GADTs, KindSignatures, LambdaCase #-}
{-# OPTIONS -Wall #-}

module Language.Hakaru.Lazy where

import Prelude hiding (Real)
import Language.Hakaru.Syntax (Real, Prob, Measure, Number, Fraction(..),
       EqType(Refl), Order(..), Base(..), Mochastic(..), weight, equal_,
       Lambda(..), Lub(..))
import Language.Hakaru.PrettyPrint (PrettyPrint, runPrettyPrint, leftMode)
import Language.Hakaru.Simplify (Simplifiable, closeLoop, simplify)
import Language.Hakaru.Any (Any(unAny))
import Data.Typeable (Typeable)
import Text.PrettyPrint (Doc)
import Control.Monad (liftM, liftM2)
import Data.Maybe (isNothing)
import Data.Function (on)
import Unsafe.Coerce (unsafeCoerce)

finally :: (Monad m) => (a -> m ()) -> a -> m a
finally k a = k a >> return a

unpair' :: (Base repr) =>
           repr (a,b) -> ((repr a, repr b) -> repr c) -> repr c
unpair' ab c = unpair ab (curry c)

uneither' :: (Base repr) =>
             repr (Either a b) -> (Either (repr a) (repr b) -> repr c) -> repr c
uneither' ab c = uneither ab (c . Left) (c . Right)

newtype M s repr a = M { unM :: forall w.
  (a -> Heap s repr -> repr (Measure w)) -> Heap s repr -> repr (Measure w) }
  -- TODO: Replace "repr (Measure w)" by "[([repr Prob], repr (Measure w))]"
  -- to optimize away "superpose [(1,...)]" and "superpose []"

instance Monad (M s repr) where
  return a = M (\c -> c a)
  m >>= k  = M (\c -> unM m (\a -> unM (k a) c))

instance (Lub repr) => Lub (M s repr) where
  bot               = M (\_ _ -> bot)
  lub (M m1) (M m2) = M (\c h -> lub (m1 c h) (m2 c h))

choice :: (Mochastic repr) => [M s repr a] -> M s repr a
choice ms = M (\c h -> superpose [ (1, m c h) | M m <- ms ])

reject :: (Mochastic repr) => M s repr a
reject = M (\_ _ -> superpose [])

insert :: (forall w. (a -> repr (Measure w)) -> repr (Measure w)) -> M s repr a
insert f = M (\c h -> f (\a -> c a h))

insert_ :: (forall w. repr (Measure w) -> repr (Measure w)) -> M s repr ()
insert_ f = insert (\m -> f (m ()))

lift :: (Mochastic repr) => repr (Measure a) -> M s repr (repr a)
lift m = insert (bind m)

cond, condN :: (Mochastic repr) => repr Bool -> repr (Measure w) ->
                                                repr (Measure w)
cond  b m = if_ b m (superpose [])
condN b m = if_ b (superpose []) m

data Lazy s (repr :: * -> *) a = Lazy
  { forward  :: M s repr (Whnf s repr a)
  , backward :: {- Number a => -} repr a -> M s repr () }

lazy :: (Lub repr) => M s repr (Whnf s repr a) -> Lazy s repr a
lazy m = Lazy m (const bot)

join :: M s repr (Lazy s repr a) -> Lazy s repr a
join m = Lazy (m >>= forward) (\t -> m >>= (`backward` t))

instance (Lub repr) => Lub (Lazy s repr) where
  bot = Lazy bot (const bot)
  lub (Lazy f1 b1) (Lazy f2 b2) = Lazy (lub f1 f2) (\t -> lub (b1 t) (b2 t))

-- TODO: Whnf,Binding,Retrieval for lists and vectors
data Whnf s (repr :: * -> *) a where
  Pair    :: Lazy s repr a -> Lazy s repr b -> Whnf s repr (a,b)
  Inl     :: Lazy s repr a ->                  Whnf s repr (Either a b)
  Inr     :: Lazy s repr b ->                  Whnf s repr (Either a b)
  Value   :: repr a ->                         Whnf s repr a
  Measure :: Lazy s repr a ->                  Whnf s repr (Measure a)

evaluate :: (Mochastic repr) => Lazy s repr a -> M s repr (repr a)
evaluate z = forward z >>= \case
  Pair x y  -> liftM2 pair (evaluate x) (evaluate y)
  Inl x     -> liftM inl (evaluate x)
  Inr y     -> liftM inr (evaluate y)
  Value a   -> return a
  Measure x -> do determineHeap
                  -- Because the heap is duplicated below, we better first
                  -- get rid of Bind and Iftrue and Iffalse and Weight in
                  -- the heap, and that's what determineHeap above does.
                  M (\c h -> c (unM (do a <- evaluate x
                                        determineHeap
                                        return (dirac a))
                                    const
                                    h) -- the heap is duplicated between here...
                               h)      -- ...and here

runLazy :: (Mochastic repr, Lub repr) =>
           (forall s. Lazy s repr (Measure a)) -> repr (Measure a)
runLazy m = unM (evaluate m) const Heap{fresh=0,bound=[]}

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
  Let     :: Loc s a ->            Whnf s repr a            -> Binding s repr
  Unpair  :: Loc s a -> Loc s b -> Lazy s repr (a,b)        -> Binding s repr
  Uninl   :: Loc s a ->            Lazy s repr (Either a b) -> Binding s repr
  Uninr   :: Loc s b ->            Lazy s repr (Either a b) -> Binding s repr
  Iftrue  ::                       Lazy s repr Bool         -> Binding s repr
  Iffalse ::                       Lazy s repr Bool         -> Binding s repr
  Weight  ::                       Lazy s repr Prob         -> Binding s repr

store :: Binding s repr -> M s repr ()
store entry = M (\c h -> c () h{bound = entry : bound h})

update :: Loc s a -> Whnf s repr a -> M s repr ()
update l result = store (Let l result)

determineHeap :: (Mochastic repr) => M s repr ()
determineHeap = pop >>= \case
  Nothing -> return ()
  Just entry -> determineHeap >> case entry of
    Bind   l   y -> evaluate y >>= \x -> update l (Value x)
    Iftrue     y -> evaluate y >>= \x -> insert_ (cond   x)
    Iffalse    y -> evaluate y >>= \x -> insert_ (condN  x)
    Weight     y -> evaluate y >>= \x -> insert_ (weight x)
    Let    _   _ -> store entry
    Unpair _ _ _ -> store entry
    Uninl  _   _ -> store entry
    Uninr  _   _ -> store entry
  where pop = M (\c h -> case bound h of
          []            -> c Nothing      h
          entry:entries -> c (Just entry) h{bound=entries})

data Retrieval s repr a where
  RBind  :: Lazy s repr a ->                Retrieval s repr a
  RLet   :: Whnf s repr a ->                Retrieval s repr a
  RFst   :: Loc s b -> Lazy s repr (a,b) -> Retrieval s repr a
  RSnd   :: Loc s a -> Lazy s repr (a,b) -> Retrieval s repr b
  RInl   :: Lazy s repr (Either a b) ->     Retrieval s repr a
  RInr   :: Lazy s repr (Either a b) ->     Retrieval s repr b

locate :: Loc s a -> Binding s repr -> Maybe (Retrieval s repr a)
locate l (Bind   l1    rhs) = fmap (\Refl -> RBind rhs) (jmEq l l1)
locate l (Let    l1    rhs) = fmap (\Refl -> RLet  rhs) (jmEq l l1)
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
locate _ (Weight       _  ) = Nothing

retrieve :: Loc s a -> (Retrieval s repr a -> M s repr w) -> M s repr w
retrieve l k = M (\c h ->
  let loop []        _     = error ("Unbound location " ++ show l)
      loop (b:older) newer = case locate l b of
        Nothing -> loop older (b:newer)
        Just r | all (isNothing . locate l) older ->
          unM (k r) (\w h' -> c w h'{bound = reverse newer ++ bound h'})
                    h{bound = older}
        _ -> error ("Duplicate heap entry " ++ show l)
  in loop (bound h) [])

memo :: (Mochastic repr, Lub repr) => Lazy s repr a -> M s repr (Lazy s repr a)
memo m = do l <- gensym
            store (Bind l m)
            return (lazyLoc l)

lazyLoc :: (Mochastic repr, Lub repr) => Loc s a -> Lazy s repr a
lazyLoc l = Lazy (fwdLoc l) (bwdLoc l)

fwdLoc :: (Mochastic repr) => Loc s a -> M s repr (Whnf s repr a)
fwdLoc l = retrieve l $ \case
  RBind rhs -> forward rhs >>= finally (update l)
  RLet rhs -> finally (update l) rhs
  RFst l2 rhs -> forward rhs >>= \case
    Pair a b -> do store (Bind l2 b)
                   forward a >>= finally (update l)
    Value ab -> do (a, b) <- insert (unpair' ab)
                   update l2 (Value b)
                   finally (update l) (Value a)
  RSnd l1 rhs -> forward rhs >>= \case
    Pair a b -> do store (Bind l1 a)
                   forward b >>= finally (update l)
    Value ab -> do (a, b) <- insert (unpair' ab)
                   update l1 (Value a)
                   finally (update l) (Value b)
  RInl rhs -> forward rhs >>= \case
    Inl a    -> forward a >>= finally (update l)
    Inr _    -> reject
    Value ab -> insert (uneither' ab) >>= \case
                  Left  a -> finally (update l) (Value a)
                  Right _ -> reject
  RInr rhs -> forward rhs >>= \case
    Inr b    -> forward b >>= finally (update l)
    Inl _    -> reject
    Value ab -> insert (uneither' ab) >>= \case
                  Right a -> finally (update l) (Value a)
                  Left  _ -> reject

bwdLoc :: (Mochastic repr, Lub repr) => Loc s a -> repr a -> M s repr ()
bwdLoc l t = retrieve l $ \case
  RBind rhs -> backward rhs t >> update l (Value t)
  RLet _ -> bot
  RFst l2 rhs -> forward rhs >>= \case
    Pair a b -> do store (Bind l2 b)
                   backward a t >> update l (Value t)
    Value _ -> bot
  RSnd l1 rhs -> forward rhs >>= \case
    Pair a b -> do store (Bind l1 a)
                   backward b t >> update l (Value t)
    Value _ -> bot
  RInl rhs -> forward rhs >>= \case
    Inl a   -> backward a t >> update l (Value t)
    Inr _   -> reject
    Value _ -> bot
  RInr rhs -> forward rhs >>= \case
    Inr b   -> backward b t >> update l (Value t)
    Inl _   -> reject
    Value _ -> bot

scalar0 :: (Lub repr) => repr a -> Lazy s repr a
scalar0 op = lazy (return (Value op))

scalar1 :: (Lub repr) => (repr a -> repr b) -> Lazy s repr a -> Lazy s repr b
scalar1 op m = lazy (do Value a <- forward m
                        return (Value (op a)))

scalar2 :: (Lub repr) => (repr a -> repr b -> repr c) ->
           Lazy s repr a -> Lazy s repr b -> Lazy s repr c
scalar2 op m n = lazy (do Value a <- forward m
                          Value b <- forward n
                          return (Value (op a b)))

instance (Lub repr, Order repr a) => Order (Lazy s repr) a where
  less  = scalar2 less
  equal = scalar2 equal

add :: (Mochastic repr, Lub repr, Num (repr a), Number a) =>
       Lazy s repr a -> Lazy s repr a -> Lazy s repr a
add x y = Lazy
  ((liftM2 ((Value.) . (+)) `on` evaluate) x y)
  (\t -> lub (forward x >>= \(Value r) -> backward y (t - r))
             (forward y >>= \(Value r) -> backward x (t - r)))

sub :: (Mochastic repr, Lub repr, Num (repr a), Number a) =>
       Lazy s repr a -> Lazy s repr a -> Lazy s repr a
sub x y = Lazy
  ((liftM2 ((Value.) . (-)) `on` evaluate) x y)
  (\t -> lub (forward x >>= \(Value r) -> backward y (r - t))
             (forward y >>= \(Value r) -> backward x (r + t)))

neg :: (Mochastic repr, Num (repr a), Number a) =>
       Lazy s repr a -> Lazy s repr a
neg x = Lazy
  (liftM (Value . negate) (evaluate x))
  (\t -> backward x (negate t))

abz :: (Mochastic repr, Num (repr a), Order repr a) =>
       Lazy s repr a -> Lazy s repr a
abz x = Lazy
  (liftM (Value . abs) (evaluate x))
  (\t -> lift (if_ (less 0 t) (superpose [(1, dirac t), (1, dirac (-t))])
                              (cond (equal 0 t) (dirac 0)))
         >>= backward x)

mul :: (Mochastic repr, Lub repr, Fraction a, Fractional (repr a)) =>
       Lazy s repr a -> Lazy s repr a -> Lazy s repr a
mul x y = Lazy
  ((liftM2 ((Value.) . (*)) `on` evaluate) x y)
  (\t -> lub (do Value r <- forward x
                 insert_ (weight (recip (unsafeProbFraction (abs r))))
                 backward y (t / r))
             (do Value r <- forward y
                 insert_ (weight (recip (unsafeProbFraction (abs r))))
                 backward x (t / r)))

inv :: (Mochastic repr, Lub repr, Fraction a, Fractional (repr a)) =>
       Lazy s repr a -> Lazy s repr a
inv x = Lazy
    (liftM (Value . recip) (evaluate x))
    (\t -> do insert_ (weight (recip (unsafeProbFraction (t * t))))
              backward x (recip t))

instance (Mochastic repr, Lub repr) => Num (Lazy s repr Int) where
  (+) = add
  (-) = sub
  (*) = scalar2 (*) -- TODO backward multiplication for Int
  negate = neg
  abs = abz
  signum x = Lazy
    (liftM (Value . signum) (evaluate x))
    (\t -> do n <- lift counting
              insert_ (cond (equal (signum n) t))
              backward x n)
  fromInteger x = Lazy
    (return (Value (fromInteger x)))
    (\t -> insert_ (cond (equal (fromInteger x) t)))

instance (Mochastic repr, Lub repr) => Num (Lazy s repr Real) where
  (+) = add
  (-) = sub
  (*) = mul
  negate = neg
  abs = abz
  signum = scalar1 signum
  fromInteger = scalar0 . fromInteger

instance (Mochastic repr, Lub repr) => Num (Lazy s repr Prob) where
  (+) = add
  (-) = sub
  (*) = mul
  negate = neg
  abs = abz
  signum = scalar1 signum
  fromInteger = scalar0 . fromInteger

instance (Mochastic repr, Lub repr) => Fractional (Lazy s repr Real) where
  recip = inv
  fromRational = scalar0 . fromRational
  -- TODO fill in (/)

instance (Mochastic repr, Lub repr) => Fractional (Lazy s repr Prob) where
  recip = inv
  fromRational = scalar0 . fromRational
  -- TODO fill in (/)

instance (Mochastic repr, Lub repr) => Floating (Lazy s repr Real) where
  pi = scalar0 pi
  exp x = Lazy
    (liftM (Value . exp) (evaluate x))
    (\t -> do insert_ (cond (less 0 t) . weight (recip (unsafeProb t)))
              backward x (log t))
  log x = Lazy
    (liftM (Value . log) (evaluate x))
    (\t -> do insert_ (weight (exp_ t))
              backward x (exp t))
  -- TODO fill in other methods

unpairM :: (Mochastic repr, Lub repr) => Lazy s repr (a,b) ->
           M s repr (Lazy s repr a, Lazy s repr b)
unpairM ab = do l1 <- gensym
                l2 <- gensym
                store (Unpair l1 l2 ab)
                return (lazyLoc l1, lazyLoc l2)

uneitherM :: (Mochastic repr, Lub repr) => Lazy s repr (Either a b) ->
             M s repr (Either (Lazy s repr a) (Lazy s repr b))
uneitherM ab = choice [do l <- gensym
                          store (Uninl l ab)
                          return (Left (lazyLoc l)),
                       do l <- gensym
                          store (Uninr l ab)
                          return (Right (lazyLoc l))]

instance (Mochastic repr, Lub repr) => Base (Lazy s repr) where
  unit              = scalar0 unit
  pair a b          = lazy (return (Pair a b))
  unpair ab k       = join (liftM (uncurry k) (unpairM ab))
  inl a             = lazy (return (Inl a))
  inr b             = lazy (return (Inr b))
  uneither ab ka kb = join (liftM (either ka kb) (uneitherM ab))
  true              = scalar0 true
  false             = scalar0 false
  if_ b t f         = join (choice [store (Iftrue  b) >> return t,
                                    store (Iffalse b) >> return f])
  unsafeProb x = Lazy
    (liftM (Value . unsafeProb) (evaluate x))
    (\t -> backward x (fromProb t))
  fromProb x = Lazy
    (liftM (Value . fromProb) (evaluate x))
    (\t -> do insert_ (cond (less 0 t))
              backward x (unsafeProb t))
  fromInt = scalar1 fromInt
  pi_ = scalar0 pi_
  exp_ x = Lazy
    (liftM (Value . exp_) (evaluate x))
    (\t -> do insert_ (weight (recip t))
              backward x (log_ t))
  log_ x = Lazy
    (liftM (Value . log_) (evaluate x))
    (\t -> do insert_ (weight (exp_ t))
              backward x (exp_ t))
  -- TODO fill in other methods
  erf = scalar1 erf -- need InvErf to disintegrate Erf
  erf_ = scalar1 erf_ -- need InvErf to disintegrate Erf
  infinity = scalar0 infinity
  negativeInfinity = scalar0 negativeInfinity
  gammaFunc = scalar1 gammaFunc
  betaFunc = scalar2 betaFunc

measure :: (Lub repr) => Lazy s repr a -> Lazy s repr (Measure a)
measure = lazy . return . Measure

unMeasure :: (Mochastic repr, Lub repr) =>
             Whnf s repr (Measure a) -> Lazy s repr a
unMeasure (Measure m) = m
unMeasure (Value m) = lazy (liftM Value (lift m))

instance (Mochastic repr, Lub repr) => Mochastic (Lazy s repr) where
  dirac x       = measure $ x
  bind m k      = measure $ join (forward m >>= memo . unMeasure >>= \a ->
                                  forward (k a) >>= return . unMeasure)
  lebesgue      = measure $ Lazy (liftM Value (lift lebesgue))
                                 (const (return ()))
  counting      = measure $ Lazy (liftM Value (lift counting))
                                 (const (return ()))
  superpose pms = measure $ join $ choice
    [ store (Weight p) >> forward m >>= return . unMeasure | (p,m) <- pms ]
  -- TODO fill in other methods

class Backward ab a where
  backward_ :: (Mochastic repr, Lub repr) =>
               Lazy s repr ab -> Lazy s repr a -> M s repr ()

instance Backward a () where
  backward_ _ _ = return ()

instance Backward Bool Bool where
  backward_ a x = store (Iftrue (equal_ a x))

instance Backward Int Int where
  backward_ a x = evaluate x >>= backward a

instance Backward Real Real where
  backward_ a x = evaluate x >>= backward a

instance Backward Prob Prob where
  backward_ a x = evaluate x >>= backward a

instance (Backward ab1 a1, Backward ab2 a2) =>
         Backward (ab1,ab2) (a1,a2) where
  backward_ ab xy = do (a,b) <- unpairM ab
                       (x,y) <- unpairM xy
                       backward_ a x
                       backward_ b y

instance (Backward ab1 a1, Backward ab2 a2) =>
         Backward (Either ab1 ab2) (Either a1 a2) where
  backward_ ab xy = do a_b <- uneitherM ab
                       x_y <- uneitherM xy
                       case (a_b, x_y) of
                         (Left  a, Left  x) -> backward_ a x
                         (Right b, Right y) -> backward_ b y
                         _                  -> reject

disintegrate :: (Mochastic repr, Lub repr, Backward ab a) => Lazy s repr a ->
                Lazy s repr (Measure ab) -> Lazy s repr (Measure ab)
disintegrate x m = measure $ join $ (forward m >>= memo . unMeasure >>= \a ->
                                     backward_ a x >> return a)

try :: (forall s. Lazy s PrettyPrint (Measure (Real, b))) ->
       PrettyPrint (Real -> Measure (Real, b))
try m = lam (\t -> runLazy (disintegrate (pair (scalar0 t) unit) m))

recover :: (Typeable a) => PrettyPrint a -> IO (Any a)
recover hakaru = closeLoop ("Any (" ++ leftMode (runPrettyPrint hakaru) ++ ")")

simp :: (Simplifiable a) => Any a -> IO (Any a)
simp = simplify . unAny

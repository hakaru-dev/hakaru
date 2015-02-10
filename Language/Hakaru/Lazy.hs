{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts, FlexibleInstances,
             Rank2Types, GADTs, KindSignatures, LambdaCase #-}
{-# OPTIONS -Wall #-}

module Language.Hakaru.Lazy where

import Prelude hiding (Real)
import Language.Hakaru.Syntax (Real, Prob, Measure, Vector,
       Number, Fraction(..), EqType(Refl), Order(..), Base(..),
       Mochastic(..), weight, equal_, Lambda(..), Lub(..))
import Language.Hakaru.PrettyPrint (PrettyPrint, runPrettyPrint, leftMode)
import Language.Hakaru.Simplify (Simplifiable, closeLoop, simplify)
import Language.Hakaru.Any (Any(unAny))
import Data.Typeable (Typeable)
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

unlist' :: (Base repr) =>
           repr [a] -> (Maybe (repr a, repr [a]) -> repr c) -> repr c
unlist' ab c = unlist ab (c Nothing) (curry (c . Just))

data M s repr a
  = Return a
  | M (forall w. (a -> Heap s repr -> repr (Measure w))
                    -> Heap s repr -> repr (Measure w))
  -- TODO: Replace "repr (Measure w)" by "[([repr Prob], repr (Measure w))]"
  -- to optimize away "superpose [(1,...)]" and "superpose []"

unM :: M s repr a -> forall w. (a -> Heap s repr -> repr (Measure w))
                                  -> Heap s repr -> repr (Measure w)
unM (Return a) = \c -> c a
unM (M m)      = m

instance Monad (M s repr) where
  return         = Return
  Return a >>= k = k a
  M m      >>= k = M (\c -> m (\a -> unM (k a) c))

instance (Lub repr) => Lub (M s repr) where
  bot       = M (\_ _ -> bot)
  lub m1 m2 = M (\c h -> lub (unM m1 c h) (unM m2 c h))

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

data Whnf s (repr :: * -> *) a where
  Pair    :: Lazy s repr a -> Lazy s repr b ->     Whnf s repr (a,b)
  True_   ::                                       Whnf s repr Bool
  False_  ::                                       Whnf s repr Bool
  Inl     :: Lazy s repr a ->                      Whnf s repr (Either a b)
  Inr     :: Lazy s repr b ->                      Whnf s repr (Either a b)
  Nil     ::                                       Whnf s repr [a]
  Cons    :: Lazy s repr a -> Lazy s repr [a] ->   Whnf s repr [a]
  Value   :: repr a ->                             Whnf s repr a
  Measure :: Lazy s repr a ->                      Whnf s repr (Measure a)
  Vector  :: Loc s (Vector a) ->                   Whnf s repr (Vector a)

determine :: (Lub repr) => Lazy s repr a -> M s repr (Whnf s repr a)
determine z = forward z >>= \case
  Pair x y     -> liftM2 Pair (liftM (lazy . return) (determine x))
                              (liftM (lazy . return) (determine y))
  Inl x        -> liftM (Inl . lazy . return) (determine x)
  Inr y        -> liftM (Inr . lazy . return) (determine y)
  Cons x y     -> liftM2 Cons (liftM (lazy . return) (determine x))
                              (liftM (lazy . return) (determine y))
  w            -> return w

evaluate :: (Mochastic repr, Lub repr) =>
            Lazy s repr a -> M s repr (repr a)
evaluate z = forward z >>= \case
  Pair x y  -> liftM2 pair (evaluate x) (evaluate y)
  True_     -> return true
  False_    -> return false
  Inl x     -> liftM inl (evaluate x)
  Inr y     -> liftM inr (evaluate y)
  Nil       -> return nil
  Cons x y  -> liftM2 cons (evaluate x) (evaluate y)
  Value a   -> return a
  Measure x -> liftM (evaluateMeasure x) duplicateHeap
  v@(Vector _) -> retrieveVector v return $ \l lo hi table f ->
                  evaluateVector lo hi table f >>= finally (update l . Value)

duplicateHeap :: (Mochastic repr, Lub repr) => M s repr (Heap s repr)
duplicateHeap = do determineHeap
                   -- Because the heap is duplicated below, we better first get
                   -- rid of Bind,Iftrue,Iffalse,Weight,Uninl,Uninr,Unnil,Uncons
                   -- in the heap, and that's what determineHeap above does.
                   M (\c h -> c h{- !duplicated heap! -} h)

evaluateMeasure :: (Mochastic repr, Lub repr) =>
                   Lazy s repr a -> Heap s repr -> repr (Measure a)
-- Call duplicateHeap before evaluateMeasure!
evaluateMeasure z = unM (do a <- evaluate z
                            determineHeap
                            return (dirac a))
                        const

evaluateVector :: (Mochastic repr, Lub repr) =>
                  Lazy s repr Int -> Lazy s repr Int ->
                  [(Lazy s repr Int, Lazy s repr b)] ->
                  (Lazy s repr Int -> Lazy s repr b) ->
                  M s repr (repr (Vector b))
evaluateVector lo hi table f = do
  lo' <- evaluate lo
  hi' <- evaluate hi
  table' <- mapM (\(j,y) -> liftM2 (,) (evaluate j) (evaluate y)) table
  heap <- duplicateHeap
  let g = foldr (\(j,y) c i -> if_ (equal i j) (dirac y) (c i))
                (\i -> evaluateMeasure (f (scalar0 i)) heap)
                table'
  lift (plate (vector lo' hi' g))

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
  Bind    :: Loc s a ->              Lazy s repr a            -> Binding s repr
  Let     :: Loc s a ->              Whnf s repr a            -> Binding s repr
  Unpair  :: Loc s a -> Loc s b ->   Lazy s repr (a,b)        -> Binding s repr
  Iftrue  ::                         Lazy s repr Bool         -> Binding s repr
  Iffalse ::                         Lazy s repr Bool         -> Binding s repr
  Uninl   :: Loc s a ->              Lazy s repr (Either a b) -> Binding s repr
  Uninr   :: Loc s b ->              Lazy s repr (Either a b) -> Binding s repr
  Unnil   ::                         Lazy s repr [a]          -> Binding s repr
  Uncons  :: Loc s a -> Loc s [a] -> Lazy s repr [a]          -> Binding s repr
  Weight  ::                         Lazy s repr Prob         -> Binding s repr
  VBind   :: Loc s (Vector b) -> Lazy s repr Int -> Lazy s repr Int ->
                           [(Lazy s repr Int, Lazy s repr b)] ->
                           (Lazy s repr Int -> Lazy s repr b) -> Binding s repr

store :: Binding s repr -> M s repr ()
store entry = M (\c h -> c () h{bound = entry : bound h})

update :: Loc s a -> Whnf s repr a -> M s repr ()
update l result = store (Let l result)

determineHeap :: (Mochastic repr, Lub repr) => M s repr ()
determineHeap = pop >>= \case
  Nothing -> return ()
  Just entry -> determineHeap >> case entry of
    Bind   l   rhs -> determine rhs >>= update l
    Iftrue     rhs -> forward rhs >>= \case
                      True_   -> return ()
                      False_  -> reject
                      Value x -> insert_ (cond   x)
    Iffalse    rhs -> forward rhs >>= \case
                      False_  -> return ()
                      True_   -> reject
                      Value x -> insert_ (condN  x)
    Uninl  l   rhs -> forward rhs >>= \case
                      Inl a    -> determine a >>= update l
                      Inr _    -> reject
                      Value ab -> insert (uneither' ab) >>= \case
                                    Left  a -> update l (Value a)
                                    Right _ -> reject
    Uninr  l   rhs -> forward rhs >>= \case
                      Inr a    -> determine a >>= update l
                      Inl _    -> reject
                      Value ab -> insert (uneither' ab) >>= \case
                                    Right a -> update l (Value a)
                                    Left  _ -> reject
    Unnil      rhs -> forward rhs >>= \case
                      Nil      -> return ()
                      Cons _ _ -> reject
                      Value ab -> insert (unlist' ab) >>= \case
                                    Nothing -> return ()
                                    Just _  -> reject
    Uncons l r rhs -> forward rhs >>= \case
                      Nil      -> return ()
                      Cons a b -> determine a >>= update l >>
                                  determine b >>= update r
                      Value ab -> insert (unlist' ab) >>= \case
                                    Just (x,y) -> update l (Value x) >>
                                                  update r (Value y)
                                    Nothing    -> reject
    Weight     rhs -> forward rhs >>= \(Value x) -> insert_ (weight x)
    Let    _   _   -> store entry
    Unpair _ _ _   -> store entry
    VBind l lo hi table f -> evaluateVector lo hi table f >>= update l . Value
  where pop = M (\c h -> case bound h of
          []            -> c Nothing      h
          entry:entries -> c (Just entry) h{bound=entries})

data Retrieval s repr a where
  RBind  :: Lazy s repr a ->                    Retrieval s repr a
  RLet   :: Whnf s repr a ->                    Retrieval s repr a
  RFst   :: Loc s b -> Lazy s repr (a,b) ->     Retrieval s repr a
  RSnd   :: Loc s a -> Lazy s repr (a,b) ->     Retrieval s repr b
  RInl   :: Lazy s repr (Either a b) ->         Retrieval s repr a
  RInr   :: Lazy s repr (Either a b) ->         Retrieval s repr b
  RCar   :: Loc s [a] -> Lazy s repr [a] ->     Retrieval s repr a
  RCdr   :: Loc s a   -> Lazy s repr [a] ->     Retrieval s repr [a]
  RVBind :: Lazy s repr Int -> Lazy s repr Int ->
            [(Lazy s repr Int, Lazy s repr b)] ->
            (Lazy s repr Int -> Lazy s repr b) -> Retrieval s repr (Vector b)

locate :: Loc s a -> Binding s repr -> Maybe (Retrieval s repr a)
locate l (Bind   l1    rhs) =  fmap (\Refl -> RBind   rhs) (jmEq l l1)
locate l (Let    l1    rhs) =  fmap (\Refl -> RLet    rhs) (jmEq l l1)
locate l (Uninl  l1    rhs) =  fmap (\Refl -> RInl    rhs) (jmEq l l1)
locate l (Uninr  l2    rhs) =  fmap (\Refl -> RInr    rhs) (jmEq l l2)
locate l (Unpair l1 l2 rhs) = unique ("Unpair duplicates variable " ++ show l)
                              (fmap (\Refl -> RFst l2 rhs) (jmEq l l1))
                              (fmap (\Refl -> RSnd l1 rhs) (jmEq l l2))
locate l (Uncons l1 l2 rhs) = unique ("Uncons duplicates variable " ++ show l)
                              (fmap (\Refl -> RCar l2 rhs) (jmEq l l1))
                              (fmap (\Refl -> RCdr l1 rhs) (jmEq l l2))
locate _ (Unnil        _  ) = Nothing
locate _ (Iftrue       _  ) = Nothing
locate _ (Iffalse      _  ) = Nothing
locate _ (Weight       _  ) = Nothing
locate l (VBind l1 lo hi table f) = fmap (\Refl -> RVBind lo hi table f)
                                         (jmEq l l1)

unique :: String -> Maybe a -> Maybe a -> Maybe a
unique e   (Just _) (Just _) = error e
unique _ a@(Just _) Nothing  = a
unique _   Nothing  a        = a

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

retrieveVector :: Whnf s repr (Vector b) ->
                  (repr (Vector b) -> M s repr w) ->
                  (Loc s (Vector b) ->
                   Lazy s repr Int -> Lazy s repr Int ->
                   [(Lazy s repr Int, Lazy s repr b)] ->
                   (Lazy s repr Int -> Lazy s repr b) -> M s repr w) ->
                  M s repr w
retrieveVector (Value v) k _ = k v
retrieveVector (Vector l) kValue kRVBind = retrieve l $ \case
  RLet v -> do result <- retrieveVector v kValue kRVBind
               update l v
               return result
  RVBind lo hi table f -> kRVBind l lo hi table f

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
  RCar l2 rhs -> forward rhs >>= \case
    Nil      -> reject
    Cons a b -> do store (Bind l2 b)
                   forward a >>= finally (update l)
    Value ab -> insert (unlist' ab) >>= \case
                  Nothing    -> reject
                  Just (a,b) -> do update l2 (Value b)
                                   finally (update l) (Value a)
  RCdr l1 rhs -> forward rhs >>= \case
    Nil      -> reject
    Cons a b -> do store (Bind l1 a)
                   forward b >>= finally (update l)
    Value ab -> insert (unlist' ab) >>= \case
                  Nothing    -> reject
                  Just (a,b) -> do update l1 (Value a)
                                   finally (update l) (Value b)
  RVBind _ _ _ _ -> return (Vector l)

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
  RCar l2 rhs -> forward rhs >>= \case
    Nil      -> reject
    Cons a b -> do store (Bind l2 b)
                   backward a t >> update l (Value t)
    Value _  -> bot
  RCdr l1 rhs -> forward rhs >>= \case
    Nil      -> reject
    Cons a b -> do store (Bind l1 a)
                   backward b t >> update l (Value t)
    Value _  -> bot
  RVBind _ _ _ _ -> bot

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

neg :: (Mochastic repr, Lub repr, Num (repr a), Number a) =>
       Lazy s repr a -> Lazy s repr a
neg x = Lazy
  (liftM (Value . negate) (evaluate x))
  (\t -> backward x (negate t))

abz :: (Mochastic repr, Lub repr, Num (repr a), Order repr a) =>
       Lazy s repr a -> Lazy s repr a
abz x = Lazy
  (liftM (Value . abs) (evaluate x))
  (\t -> lift (if_ (less 0 t) (superpose [(1, dirac t), (1, dirac (-t))])
                              (cond (equal 0 t) (dirac 0)))
         >>= backward x)

mul :: (Mochastic repr, Lub repr,
        Fraction a, Fractional (repr a)) =>
       Lazy s repr a -> Lazy s repr a -> Lazy s repr a
mul x y = Lazy
  ((liftM2 ((Value.) . (*)) `on` evaluate) x y)
  (\t -> lub (do Value r <- forward x
                 insert_ (weight (recip (unsafeProbFraction (abs r))))
                 backward y (t / r))
             (do Value r <- forward y
                 insert_ (weight (recip (unsafeProbFraction (abs r))))
                 backward x (t / r)))

inv :: (Mochastic repr, Lub repr,
        Fraction a, Fractional (repr a)) =>
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

instance (Mochastic repr, Lub repr) =>
         Fractional (Lazy s repr Real) where
  recip = inv
  fromRational = scalar0 . fromRational
  -- TODO fill in (/)

instance (Mochastic repr, Lub repr) =>
         Fractional (Lazy s repr Prob) where
  recip = inv
  fromRational = scalar0 . fromRational
  -- TODO fill in (/)

instance (Mochastic repr, Lub repr) =>
         Floating (Lazy s repr Real) where
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
unpairM (Lazy (Return (Pair a b)) _) = Return (a, b)
unpairM ab = do l1 <- gensym
                l2 <- gensym
                store (Unpair l1 l2 ab)
                return (lazyLoc l1, lazyLoc l2)

ifM :: (Mochastic repr, Lub repr) => Lazy s repr Bool -> M s repr Bool
ifM (Lazy (Return True_ ) _) = Return True
ifM (Lazy (Return False_) _) = Return False
ifM ab = choice [store (Iftrue  ab) >> return True,
                 store (Iffalse ab) >> return False]

uneitherM :: (Mochastic repr, Lub repr) => Lazy s repr (Either a b) ->
             M s repr (Either (Lazy s repr a) (Lazy s repr b))
uneitherM (Lazy (Return (Inl a)) _) = Return (Left  a)
uneitherM (Lazy (Return (Inr a)) _) = Return (Right a)
uneitherM ab = choice [do l <- gensym
                          store (Uninl l ab)
                          return (Left (lazyLoc l)),
                       do l <- gensym
                          store (Uninr l ab)
                          return (Right (lazyLoc l))]

unlistM :: (Mochastic repr, Lub repr) => Lazy s repr [a] ->
           M s repr (Maybe (Lazy s repr a, Lazy s repr [a]))
unlistM (Lazy (Return Nil       ) _) = Return Nothing
unlistM (Lazy (Return (Cons a b)) _) = Return (Just (a,b))
unlistM ab = choice [do store (Unnil ab)
                        return Nothing,
                     do l1 <- gensym
                        l2 <- gensym
                        store (Uncons l1 l2 ab)
                        return (Just (lazyLoc l1, lazyLoc l2))]

instance (Mochastic repr, Lub repr) => Base (Lazy s repr) where
  unit              = scalar0 unit
  pair a b          = lazy (return (Pair a b))
  unpair ab k       = join (liftM (uncurry k) (unpairM ab))
  inl a             = lazy (return (Inl a))
  inr b             = lazy (return (Inr b))
  uneither ab ka kb = join (liftM (either ka kb) (uneitherM ab))
  true              = lazy (return True_)
  false             = lazy (return False_)
  if_ ab t f        = join (liftM (\b -> if b then t else f) (ifM ab))
  nil               = lazy (return Nil)
  cons a b          = lazy (return (Cons a b))
  unlist ab ka kb   = join (liftM (maybe ka (uncurry kb)) (unlistM ab))
  vector lo hi f    = lazy (do l <- gensym
                               store (VBind l lo hi [] f)
                               return (Vector l))
  loBound v         = join (forward v >>= \w -> retrieveVector w
                        (\v' -> return (scalar0 (loBound v')))
                        (\l lo hi table f ->
                         store (VBind l lo hi table f) >> return lo))
  hiBound v         = join (forward v >>= \w -> retrieveVector w
                        (\v' -> return (scalar0 (hiBound v')))
                        (\l lo hi table f ->
                         store (VBind l lo hi table f) >> return hi))
  index v i         = join (forward v >>= \w -> retrieveVector w
                        (\v' -> liftM (scalar0 . index v') (evaluate i))
                        (\l lo hi table f ->
                         choice $ do sequence_ [ store (Iffalse (equal i j))
                                               | (j,_) <- table ]
                                     x <- memo (f i)
                                     store (VBind l lo hi ((i,x):table) f)
                                     return x
                                : [ do store (Iftrue (equal i j))
                                       store (VBind l lo hi table f)
                                       return y
                                  | (j,y) <- table ]))
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

instance (Mochastic repr, Lub repr) =>
         Mochastic (Lazy s repr) where
  dirac x       = measure $ x
  bind m k      = measure $ join (forward m >>= memo . unMeasure >>= \a ->
                                  liftM unMeasure (forward (k a)))
  lebesgue      = measure $ Lazy (liftM Value (lift lebesgue))
                                 (const (return ()))
  counting      = measure $ Lazy (liftM Value (lift counting))
                                 (const (return ()))
  superpose pms = measure $ join $ choice
    [ store (Weight p) >> liftM unMeasure (forward m) | (p,m) <- pms ]
  -- TODO fill in other methods
  plate v       = measure $ lazy $ do
    let f i = join (liftM unMeasure (forward (index v i)))
    l' <- gensym
    store (VBind l' (loBound v) (hiBound v) [] f)
    return (Vector l')

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

instance (Backward ab a) => Backward [ab] [a] where
  backward_ ab xy = do a_b <- unlistM ab
                       x_y <- unlistM xy
                       case (a_b, x_y) of
                         (Nothing   , Nothing   ) -> return ()
                         (Just (a,b), Just (x,y)) -> do backward_ a x
                                                        backward_ b y
                         _                        -> reject

disintegrate :: (Mochastic repr, Lub repr, Backward ab a) =>
                Lazy s repr a ->
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

{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts, FlexibleInstances,
             Rank2Types, GADTs, DataKinds, KindSignatures, LambdaCase #-}
{-# OPTIONS -Wall #-}

module Language.Hakaru.Lazy (Lazy, runLazy, Backward, disintegrate,
       Cond, runDisintegrate, density,
       scalar0, lazy) where

import Prelude hiding (Real)
import Language.Hakaru.Syntax (Hakaru(..),
       Number(..), Fraction(..), Order(..),
       Base(..), snd_, equal_, and_, or_, not_, weight,
       Mochastic(..), Integrate(..), Lambda(..), Lub(..))
import Language.Hakaru.Compose
import Control.Monad (liftM, liftM2, ap)
import Control.Applicative (Applicative(..))
import Data.Maybe (isNothing)
import Unsafe.Coerce (unsafeCoerce)
import Language.Hakaru.Expect (Expect(Expect), Expect', total)

ifTrue, ifFalse
    :: (Mochastic repr)
    => repr 'HBool -> repr ('HMeasure w) -> repr ('HMeasure w)
ifTrue  x m = if_ x m (superpose [])
ifFalse x m = if_ x (superpose []) m

uninl
    :: (Mochastic repr)
    => repr ('HEither a b)
    -> (repr a -> repr ('HMeasure w))
    -> repr ('HMeasure w)
uninl x c = uneither x c (\_ -> superpose [])

uninr
    :: (Mochastic repr)
    => repr ('HEither a b)
    -> (repr b -> repr ('HMeasure w))
    -> repr ('HMeasure w)
uninr x c = uneither x (\_ -> superpose []) c

-- BUG: what is the kind of @a@ really supposed to be?
data M (s :: Hakaru *) (repr :: Hakaru * -> *) (a :: *)
  = Return a
  | M (forall w. (a -> Heap s repr -> repr ('HMeasure w))
                    -> Heap s repr -> repr ('HMeasure w))

unM :: M s repr a -> forall w. (a -> Heap s repr -> repr ('HMeasure w))
                                  -> Heap s repr -> repr ('HMeasure w)
unM (Return a) = \c -> c a
unM (M m)      = m

instance Functor (M s repr) where
    fmap f (Return a) = Return (f a)
    fmap f (M m)      = M (\c -> m (c . f))
    
instance Applicative (M s repr) where
    pure  = Return
    (<*>) = ap -- TODO: can we optimize this?

instance Monad (M s repr) where
    return         = Return
    Return a >>= k = k a
    M m      >>= k = M (\c -> m (\a -> unM (k a) c))

-- N.B., we can't make an actual 'Lub' instance, because the kind of @M s repr@ is wrong...

-- | Like 'Lub' but for a different kind...
-- TODO: choose better names for things!
class HaskellLub (hask :: * -> *) where
    bot_ :: hask a
    lub_ :: hask a -> hask a -> hask a

instance Lub repr => HaskellLub (M s repr) where
    bot_ = M (\_ _ -> bot)
    lub_ m1 m2 = M (\c h -> lub (unM m1 c h) (unM m2 c h))

choice :: (Mochastic repr) => [M s repr a] -> M s repr a
choice [m] = m
choice ms  = M (\c h -> superpose [ (1, m c h) | M m <- ms ])

reject :: (Mochastic repr) => M s repr a
reject = M (\_ _ -> superpose [])

insert :: (forall w. (a -> repr ('HMeasure w)) -> repr ('HMeasure w)) -> M s repr a
insert f = M (\c h -> f (\a -> c a h))

insert_ :: (forall w. repr ('HMeasure w) -> repr ('HMeasure w)) -> M s repr ()
insert_ f = insert (\m -> f (m ()))

lift :: (Mochastic repr) => repr ('HMeasure a) -> M s repr (repr a)
lift m = insert (bind m)

data Lazy (s :: Hakaru *) (repr :: Hakaru * -> *) (a :: Hakaru *) = Lazy
  { forward  :: M s repr (Hnf s repr a)
  , backward :: (Number a) => Hnf s repr a -> M s repr () }

lazy :: (Lub repr) => M s repr (Hnf s repr a) -> Lazy s repr a
lazy m = Lazy m (const bot_)

-- TODO: rename this; will clash with a Prelude name in GHC 7.10
join :: M s repr (Lazy s repr a) -> Lazy s repr a
join m = Lazy (m >>= forward) (\t -> m >>= (`backward` t))

instance (Lub repr) => Lub (Lazy s repr) where
  bot = Lazy bot_ (const bot_)
  lub (Lazy f1 b1) (Lazy f2 b2) =
    Lazy (lub_ f1 f2) (\t -> lub_ (b1 t) (b2 t))

data Hnf (s :: Hakaru *) (repr :: Hakaru * -> *) (a :: Hakaru *) where
  Pair    :: Lazy s repr a -> Lazy s repr b ->     Hnf s repr ('HPair a b)
  True_   ::                                       Hnf s repr 'HBool
  False_  ::                                       Hnf s repr 'HBool
  Inl     :: Lazy s repr a ->                      Hnf s repr ('HEither a b)
  Inr     :: Lazy s repr b ->                      Hnf s repr ('HEither a b)
  Int     :: Integer ->                            Hnf s repr 'HInt
  Real    :: Rational ->  {-constant propagation-} Hnf s repr 'HReal
  Prob    :: Rational ->  {-constant propagation-} Hnf s repr 'HProb
  Value   :: repr a ->                             Hnf s repr a
  Measure :: Lazy s repr a ->                      Hnf s repr ('HMeasure a)
  Vector  :: Lazy s repr 'HInt ->
             (Lazy s repr 'HInt -> Lazy s repr a) -> Hnf s repr ('HArray a)
  Plate   :: Loc ('HArray s) a ->                   Hnf s repr ('HArray a)
  
determine :: (Lub repr) => Lazy s repr a -> M s repr (Hnf s repr a)
determine z = forward z >>= \case
  Pair x y     -> liftM2 Pair (liftM (lazy . return) (determine x))
                              (liftM (lazy . return) (determine y))
  Inl x        -> liftM (Inl . lazy . return) (determine x)
  Inr y        -> liftM (Inr . lazy . return) (determine y)
  Vector s f   -> liftM (\s' -> Vector (lazy (return s')) f) (determine s)
  w            -> return w

forget :: (Base repr) => Hnf s repr a -> repr a
forget True_     = true
forget False_    = false
forget (Int   n) = fromInteger n
forget (Real  r) = fromRational r
forget (Prob  r) = fromRational r
forget (Value v) = v
forget _         = error "Lazy: no information to forget"

atomize :: (Mochastic repr, Lub repr) => Hnf s repr a -> M s repr (repr a)
atomize (Pair x y)   = liftM2 pair (evaluate x) (evaluate y)
atomize (Inl x)      = liftM inl (evaluate x)
atomize (Inr y)      = liftM inr (evaluate y)
atomize (Measure x)  = liftM (evaluateMeasure x) duplicateHeap
atomize (Vector s f) = evaluateVector s [] f
atomize (Plate l)    =
    let process (RVLet v)          = return v
        process (RVBind table rhs) = evaluatePlate table rhs
    in retrieve locateV l (\retrieval -> do v <- process retrieval
                                            store (VLet l v)
                                            return v)
atomize w            = return (forget w)

evaluate :: (Mochastic repr, Lub repr) =>
            Lazy s repr a -> M s repr (repr a)
evaluate z = forward z >>= atomize

duplicateHeap :: (Mochastic repr, Lub repr) => M s repr (Heap s repr)
duplicateHeap = do determineHeap
                   -- Because the heap is duplicated below, we better first get
                   -- rid of Bind,Iftrue,Iffalse,Weight,Uninl,Uninr,
                   -- in the heap, and that's what determineHeap above does.
                   M (\c h -> c h{- !duplicated heap! -} h)

evaluateMeasure :: (Mochastic repr, Lub repr) =>
                   Lazy s repr a -> Heap s repr -> repr ('HMeasure a)
-- Call duplicateHeap before evaluateMeasure!
evaluateMeasure z = unM (do a <- evaluate z
                            determineHeap
                            return (dirac a))
                        const

evaluateVector
    :: (Mochastic repr, Lub repr)
    => Lazy s repr 'HInt
    -> [(Lazy s repr 'HInt, Lazy s repr a)]
    -> (Lazy s repr 'HInt -> Lazy s repr a)
    -> M s repr (repr ('HArray a))
evaluateVector s table f = do
  s' <- evaluate s
  table' <- evaluatePairs table
  heap <- duplicateHeap
  let g i = evaluateMeasure (f (scalar0 i)) heap
  lift (plate (vector s' (override table' g)))

evaluatePlate
    :: (Mochastic repr, Lub repr)
    => [(Lazy s repr 'HInt, Lazy s repr a)]
    -> Lazy s repr ('HArray ('HMeasure a))
    -> M s repr (repr ('HArray a))
evaluatePlate table rhs = do
  size'  <- evaluate (size rhs)
  table' <- evaluatePairs table
  vm <- evaluate rhs
  lift (plate (vector size' (override table' (index vm))))

evaluatePairs
    :: (Mochastic repr, Lub repr)
    => [(Lazy s repr a, Lazy s repr b)]
    -> M s repr [(repr a, repr b)]
evaluatePairs = mapM (\(a,b) -> liftM2 (,) (evaluate a) (evaluate b))

override
    :: (Mochastic repr)
    => [(repr 'HInt, repr a)]
    -> (repr 'HInt -> repr ('HMeasure a))
    -> (repr 'HInt -> repr ('HMeasure a))
override table f = foldr (\(j,y) c i -> if_ (equal i j) (dirac y) (c i)) f table

runLazy
    :: (Mochastic repr, Lub repr)
    => (forall s. Lazy s repr ('HMeasure a))
    -> repr ('HMeasure a)
runLazy m = unM (evaluate m) const Heap{fresh=0,bound=[]}

data Heap (s :: Hakaru *) (repr :: Hakaru * -> *) = Heap
  { fresh :: Int
  , bound :: [Binding s repr] }

newtype Loc (s :: Hakaru *) (a :: Hakaru *) = Loc Int
  deriving (Show)


data EqType (t :: Hakaru *) (t' :: Hakaru *) where
  Refl :: EqType t t
  
jmEq :: Loc s a -> Loc s b -> Maybe (EqType a b)
jmEq (Loc a) (Loc b) | a == b    = Just (unsafeCoerce Refl)
                     | otherwise = Nothing

gensym :: M s repr (Loc s a)
gensym = M (\c h@Heap{fresh=f} -> c (Loc f) h{fresh = succ f})

gensymVector :: M s repr (Loc ('HArray s) a)
gensymVector = M (\c h@Heap{fresh=f} -> c (Loc f) h{fresh = succ f})

data Binding (s :: Hakaru *) (repr :: Hakaru * -> *) where
  Bind    :: Loc s a ->              Lazy s repr a              -> Binding s repr
  Let     :: Loc s a ->              Hnf s repr a               -> Binding s repr
  Unpair  :: Loc s a -> Loc s b ->   Lazy s repr ('HPair a b)   -> Binding s repr
  Iftrue  ::                         Lazy s repr 'HBool         -> Binding s repr
  Iffalse ::                         Lazy s repr 'HBool         -> Binding s repr
  Uninl   :: Loc s a ->              Lazy s repr ('HEither a b) -> Binding s repr
  Uninr   :: Loc s b ->              Lazy s repr ('HEither a b) -> Binding s repr
  Weight  ::                         Lazy s repr 'HProb         -> Binding s repr
  VBind   :: Loc ('HArray s) a -> [(Lazy s repr 'HInt, Lazy s repr a)] ->
                             Lazy s repr ('HArray ('HMeasure a)) -> Binding s repr
  VLet    :: Loc ('HArray s) a -> repr ('HArray a)              -> Binding s repr

store :: Binding s repr -> M s repr ()
store entry = M (\c h -> c () h{bound = entry : bound h})

update :: Loc s a -> Hnf s repr a -> M s repr ()
update l result = store (Let l result)

determineHeap :: (Mochastic repr, Lub repr) => M s repr ()
determineHeap = pop >>= \case Nothing -> return ()
                              Just entry -> do entries <- process entry
                                               determineHeap
                                               mapM_ store entries
  where
    pop = M (\c h -> case bound h of
          []            -> c Nothing      h
          entry:entries -> c (Just entry) h{bound=entries})
    process entry = case entry of
      Bind   l      rhs -> do x <- determine rhs
                              return [Let l x]
      Iftrue        rhs -> forward rhs >>= \case
                           True_   -> return []
                           False_  -> reject
                           Value x -> do insert_ (ifTrue x)
                                         return []
      Iffalse       rhs -> forward rhs >>= \case
                           False_  -> return []
                           True_   -> reject
                           Value x -> do insert_ (ifFalse x)
                                         return []
      Uninl  l      rhs -> forward rhs >>= \case
                           Inl a    -> do x <- determine a
                                          return [Let l x]
                           Inr _    -> reject
                           Value ab -> do a <- insert (uninl ab)
                                          return [Let l (Value a)]
      Uninr  l      rhs -> forward rhs >>= \case
                           Inr a    -> do x <- determine a
                                          return [Let l x]
                           Inl _    -> reject
                           Value ab -> do a <- insert (uninr ab)
                                          return [Let l (Value a)]
      Weight        rhs -> forward rhs >>= \case
                           Prob 0 -> reject
                           Prob 1 -> return []
                           x      -> do insert_ (weight (forget x))
                                        return []
      VBind l table rhs -> do v <- evaluatePlate table rhs
                              return [VLet l v]
      Let    _      _   -> return [entry]
      Unpair _ _    _   -> return [entry]
      VLet   _      _   -> return [entry]

data Retrieval (s :: Hakaru *) (repr :: Hakaru * -> *) (a :: Hakaru *) where
  RBind  :: Lazy s repr a ->                       Retrieval s repr a
  RLet   :: Hnf s repr a ->                        Retrieval s repr a
  RFst   :: Loc s b -> Lazy s repr ('HPair a b) -> Retrieval s repr a
  RSnd   :: Loc s a -> Lazy s repr ('HPair a b) -> Retrieval s repr b
  RInl   :: Lazy s repr ('HEither a b) ->          Retrieval s repr a
  RInr   :: Lazy s repr ('HEither a b) ->          Retrieval s repr b

data VRetrieval (s :: Hakaru *) (repr :: Hakaru * -> *) (a :: Hakaru *) where
  RVBind :: [(Lazy s repr 'HInt, Lazy s repr a)] ->
            Lazy s repr ('HArray ('HMeasure a)) -> VRetrieval s repr a
  RVLet  :: repr ('HArray a)                   -> VRetrieval s repr a

locate :: Loc s a -> Binding s repr -> Maybe (Retrieval s repr a)
locate l (Bind   l1    rhs) =  fmap (\Refl -> RBind   rhs) (jmEq l l1)
locate l (Let    l1    rhs) =  fmap (\Refl -> RLet    rhs) (jmEq l l1)
locate l (Uninl  l1    rhs) =  fmap (\Refl -> RInl    rhs) (jmEq l l1)
locate l (Uninr  l2    rhs) =  fmap (\Refl -> RInr    rhs) (jmEq l l2)
locate l (Unpair l1 l2 rhs) = unique ("Unpair duplicates variable " ++ show l)
                              (fmap (\Refl -> RFst l2 rhs) (jmEq l l1))
                              (fmap (\Refl -> RSnd l1 rhs) (jmEq l l2))
locate _ (Iftrue       _  ) = Nothing
locate _ (Iffalse      _  ) = Nothing
locate _ (Weight       _  ) = Nothing
locate _ (VBind  _ _   _  ) = Nothing
locate _ (VLet   _     _  ) = Nothing

unique :: String -> Maybe a -> Maybe a -> Maybe a
unique e   (Just _) (Just _) = error e
unique _ a@(Just _) Nothing  = a
unique _   Nothing  a        = a

locateV :: Loc ('HArray s) a -> Binding s repr -> Maybe (VRetrieval s repr a)
locateV l (VBind l1 table rhs) = fmap (\Refl -> RVBind table rhs) (jmEq l l1)
locateV l (VLet  l1       rhs) = fmap (\Refl -> RVLet        rhs) (jmEq l l1)
locateV _ _                    = Nothing

retrieve :: (Show loc) =>
            (loc -> Binding s repr -> Maybe retrieval) ->
            loc -> (retrieval -> M s repr w) -> M s repr w
retrieve look l k = M (\c h ->
  let loop []        _     = error ("Unbound location " ++ show l)
      loop (b:older) newer = case look l b of
        Nothing -> loop older (b:newer)
        Just r | all (isNothing . look l) older ->
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

fwdLoc :: (Mochastic repr) => Loc s a -> M s repr (Hnf s repr a)
fwdLoc l = retrieve locate l (\retrieval -> do result <- process retrieval
                                               update l result
                                               return result)
  where
    process (RBind   rhs) = forward rhs
    process (RLet    rhs) = return rhs
    process (RFst l2 rhs) = forward rhs >>= \case
                            Pair a b -> store (Bind l2 b) >> forward a
                            Value ab -> do (a,b) <- insert (unpair ab . curry)
                                           update l2 (Value b)
                                           return (Value a)
    process (RSnd l1 rhs) = forward rhs >>= \case
                            Pair a b -> store (Bind l1 a) >> forward b
                            Value ab -> do (a,b) <- insert (unpair ab . curry)
                                           update l1 (Value a)
                                           return (Value b)
    process (RInl    rhs) = forward rhs >>= \case
                            Inl a    -> forward a
                            Inr _    -> reject
                            Value ab -> liftM Value (insert (uninl ab))
    process (RInr    rhs) = forward rhs >>= \case
                            Inr b    -> forward b
                            Inl _    -> reject
                            Value ab -> liftM Value (insert (uninr ab))

bwdLoc :: (Mochastic repr, Lub repr, Number a) => Loc s a -> Hnf s repr a -> M s repr ()
bwdLoc l t = retrieve locate l (\retrieval -> do process retrieval
                                                 update l t)
  where
    process (RBind   rhs) = backward rhs t
    process (RLet    _  ) = bot_
    process (RFst l2 rhs) = forward rhs >>= \case
                            Pair a b -> store (Bind l2 b) >> backward a t
                            Value _  -> bot_
    process (RSnd l1 rhs) = forward rhs >>= \case
                            Pair a b -> store (Bind l1 a) >> backward b t
                            Value _  -> bot_
    process (RInl    rhs) = forward rhs >>= \case
                            Inl a    -> backward a t
                            Inr _    -> reject
                            Value _  -> bot_
    process (RInr    rhs) = forward rhs >>= \case
                            Inr b    -> backward b t
                            Inl _    -> reject
                            Value _  -> bot_

isNum :: (Number a) => Rational -> Hnf s repr a -> Bool
isNum m h = case h of
              Int n  -> fromInteger n == m
              Real n -> n == m
              Prob n -> n == m
              _      -> False
                                        
instance (Base repr, Num (repr a), Number a) => Num (Hnf s repr a) where
  x + y  = case (x,y) of
             (Int a,  Int b)  -> Int  (a+b)
             (Real a, Real b) -> Real (a+b)
             (Prob a, Prob b) -> Prob (a+b)
             (Value _, s) | isNum 0 s -> x
             (s, Value _) | isNum 0 s -> y
             _            -> Value (forget x + forget y)
  x - y  = case (x,y) of
             (Int a,  Int b)  -> Int  (a-b)
             (Real a, Real b) -> Real (a-b)
             (Prob a, Prob b) -> Prob (a-b)
             (Value _, s) | isNum 0 s -> x
             (s, Value _) | isNum 0 s -> y
             _            -> Value (forget x - forget y)
  x * y  = case (x,y) of
             (Int a,  Int b)  -> Int  (a*b)
             (Real a, Real b) -> Real (a*b)
             (Prob a, Prob b) -> Prob (a*b)
             (Value _, s) | isNum 0 s -> s
                          | isNum 1 s -> x
             (s, Value _) | isNum 0 s -> s
                          | isNum 1 s -> y
             _            -> Value (forget x * forget y)
                             
  negate (Int a)  = Int   (negate a)
  negate (Real a) = Real  (negate a)
  negate (Prob a) = Prob  (negate a)
  negate x        = Value (negate (forget x))
                    
  abs    (Int a)  = Int   (abs a)
  abs    (Real a) = Real  (abs a)
  abs    (Prob a) = Prob  (abs a)
  abs    x        = Value (abs (forget x))

  signum (Int a)  = Int   (signum a)
  signum (Real a) = Real  (signum a)
  signum (Prob a) = Prob  (signum a)
  signum x        = Value (signum (forget x))
                     
  fromInteger n = numberCase (Int n)
                             (Real (fromInteger n))
                             (Prob (fromInteger n))

instance (Base repr, Fractional (repr a), Fraction a) =>
    Fractional (Hnf s repr a) where
  recip (Real a) = Real  (recip a)
  recip (Prob a) = Prob  (recip a)
  recip x        = Value (recip (forget x))
                   
  fromRational r = fractionCase (Real r) (Prob r)
                 
  x / y = case (x,y) of
            (Real a, Real b) -> Real (a/b)
            (Prob a, Prob b) -> Prob (a/b)
            (Value _, s) | isNum 0 s -> error "Lazy: divide by zero"
                         | isNum 1 s -> x
            (s, Value _) | isNum 0 s -> s
            _ ->         Value (forget x / forget y)

atom1 :: (Base repr) => (repr a -> repr a) -> Hnf s repr a -> Hnf s repr a
atom1 op = Value . op . forget

atom2 :: (Base repr) => (repr a -> repr b -> repr c)
      -> Hnf s repr a -> Hnf s repr b -> Hnf s repr c
atom2 op a b = Value $ op (forget a) (forget b)
                         
instance (Base repr) => Floating (Hnf s repr 'HReal) where
  pi      = Value pi
  exp     = atom1 exp
  log     = atom1 log
  (**)    = atom2 (**)
  logBase = atom2 logBase
  sqrt    = atom1 sqrt
  sin     = atom1 sin
  cos     = atom1 cos
  asin    = atom1 asin
  acos    = atom1 acos
  atan    = atom1 atan
  sinh    = atom1 sinh
  cosh    = atom1 cosh
  asinh   = atom1 asinh
  acosh   = atom1 acosh
  atanh   = atom1 atanh
  
scalar0 :: (Lub repr) => repr a -> Lazy s repr a
scalar0 op = lazy (return (Value op))

scalar1 :: (Lub repr, Mochastic repr) => (repr a -> repr b) ->
           Lazy s repr a -> Lazy s repr b
scalar1 op m = lazy (liftM (Value . op) (evaluate m))

scalar2 :: (Lub repr, Mochastic repr) => (repr a -> repr b -> repr c) ->
           Lazy s repr a -> Lazy s repr b -> Lazy s repr c
scalar2 op m n = lazy (liftM2 ((Value.) . op) (evaluate m) (evaluate n))

comparison
    :: (Lub repr, Mochastic repr)
    => (Integer -> Integer -> Bool)
    -> (repr a -> repr a -> repr 'HBool)
    -> Lazy s repr a -> Lazy s repr a -> Lazy s repr 'HBool
comparison static dynamic m n = lazy $ do
  a <- forward m
  b <- forward n
  case (a,b) of (Int x, Int y) -> return (if static x y then True_ else False_)
                _ -> do x <- evaluate (lazy (return a))
                        y <- evaluate (lazy (return b))
                        return (Value (dynamic x y))

instance (Lub repr, Mochastic repr, Order repr a) => Order (Lazy s repr) a where
  less  = comparison (<)  less
  equal = comparison (==) equal

add :: (Mochastic repr, Lub repr, Num (repr a), Number a) => 
       Lazy s repr a -> Lazy s repr a -> Lazy s repr a
add x y = Lazy
          (liftM2 (+) (forward x) (forward y))
          (\t -> lub_ (forward x >>= \r -> backward y (t - r))
                      (forward y >>= \r -> backward x (t - r)))

sub :: (Mochastic repr, Lub repr, Num (repr a), Number a) => 
       Lazy s repr a -> Lazy s repr a -> Lazy s repr a
sub x y = Lazy
          (liftM2 (-) (forward x) (forward y))
          (\t -> lub_ (forward x >>= \r -> backward y (r - t))
                      (forward y >>= \r -> backward x (r + t)))

mul :: (Mochastic repr, Lub repr, Num (repr a), Number a) => 
       Lazy s repr a -> Lazy s repr a -> Lazy s repr a
mul x y = lazy (liftM2 (*) (forward x) (forward y))          
          
neg :: (Mochastic repr, Lub repr, Num (repr a), Number a) =>
       Lazy s repr a -> Lazy s repr a
neg x = Lazy (liftM negate (forward x))
             (\t -> backward x (negate t))

abz :: (Mochastic repr, Lub repr, Num (repr a), Order repr a) =>
       Lazy s repr a -> Lazy s repr a
abz x = Lazy
        (liftM abs (forward x))
        (\t -> do u <- atomize t               
                  v <- lift (if_ (less 0 u) (superpose [(1, dirac u)
                                                       ,(1, dirac (-u))])
                                            (ifTrue (equal 0 u) (dirac 0)))
                  backward x (Value v))

sign :: (Mochastic repr, Lub repr, Num (repr a), Number a) =>
        Lazy s repr a -> Lazy s repr a
sign x = lazy (liftM signum (forward x))
 
inv :: (Mochastic repr, Lub repr, Fractional (repr a), Fraction a) =>
       Lazy s repr a -> Lazy s repr a
inv x = Lazy
        (liftM recip (forward x))
        (\t -> do u <- atomize (t * t)
                  insert_ (weight (recip (unsafeProbFraction u)))
                  backward x (recip t))

divide :: (Mochastic repr, Lub repr, Fractional (repr a), Fraction a) =>
          Lazy s repr a -> Lazy s repr a -> Lazy s repr a
divide x y = Lazy
             (liftM2 (/) (forward x) (forward y))
             (\t -> lub_
                    (do r <- forward x
                        w <- atomize (abs r / (t*t))
                        insert_ (weight (unsafeProbFraction w))
                        backward y (r / t))
                    (do r <- evaluate y
                        insert_ (weight . unsafeProbFraction $ abs r)
                        backward x (t * (Value r))))

instance (Mochastic repr, Lub repr) => Num (Lazy s repr 'HInt) where
  (+) = add
  (-) = sub
  x * y = (mul x y)
    { backward = (\t -> lub_
        (do r <- evaluate x
            n <- lift counting
            u <- atomize t
            insert_ (ifTrue (equal (r * n) u))
            backward y (Value n))
        (do r <- evaluate y
            n <- lift counting
            u <- atomize t
            insert_ (ifTrue (equal (n * r) u))
            backward x (Value n))) }
  negate = neg
  abs = abz
  signum x = (sign x)
             { backward = (\t -> do n <- lift counting
                                    u <- atomize t
                                    insert_ (ifTrue (equal (signum n) u))
                                    backward x (Value n)) }
  fromInteger n = Lazy (return (fromInteger n))
                       (\t -> do u <- atomize t
                                 insert_ (ifTrue (equal (fromInteger n) u)))

instance (Mochastic repr, Lub repr) => Num (Lazy s repr 'HReal) where
  (+) = add
  (-) = sub
  x * y = (mul x y)
    { backward = (\t -> lub_
        (do r <- evaluate x
            insert_ (weight (recip (unsafeProb (abs r))))
            backward y (t / (Value r)))
        (do r <- evaluate y
            insert_ (weight (recip (unsafeProb (abs r))))
            backward x (t / (Value r)))) }
  negate = neg
  abs = abz
  signum = sign
  fromInteger = lazy . return . fromInteger

instance (Mochastic repr, Lub repr) => Num (Lazy s repr 'HProb) where
  (+) = add  
  (-) = sub
  x * y = (mul x y)
    { backward = (\t -> lub_
        (do r <- evaluate x
            insert_ (weight (recip (abs r)))
            backward y (t / (Value r)))
        (do r <- evaluate y
            insert_ (weight (recip (abs r)))
            backward x (t / (Value r)))) }
  negate = neg
  abs = abz
  signum = sign
  fromInteger = lazy . return . fromInteger

instance (Mochastic repr, Lub repr) =>
         Fractional (Lazy s repr 'HReal) where
  recip = inv
  fromRational = lazy . return . fromRational
  (/) = divide

instance (Mochastic repr, Lub repr) =>
         Fractional (Lazy s repr 'HProb) where
  recip = inv
  fromRational = lazy . return . fromRational
  (/) = divide

instance (Mochastic repr, Lub repr) =>
         Floating (Lazy s repr 'HReal) where
  pi = lazy (return pi)
  exp x = Lazy
    (liftM exp (forward x))
    (\t -> do u <- atomize t
              insert_ (ifTrue (less 0 u) . weight (recip (unsafeProb u)))
              backward x (log t))
  log x = Lazy
    (liftM log (forward x))
    (\t -> do u <- atomize t
              insert_ (weight (exp_ u))
              backward x (exp t))
  x ** y = Lazy
    (liftM2 (**) (forward x) (forward y))
    (\t -> lub_
        (do r <- forward x
            -- TODO if r is 0 or 1 then bot
            -- Maybe the (log r) in w takes care of the r=0 case
            t' <- atomize t
            insert_ (ifTrue (less 0 t'))
            w <- atomize (recip (abs (t * log r)))
            insert_ (weight (unsafeProb w))
            backward y (logBase r t))
        (do r <- forward y
            -- TODO if r is 0 then bot
            -- Maybe the weight w takes care of this case
            t'<- atomize t
            insert_ (ifTrue (less 0 t'))
            let ex = t ** (recip r)
            w <- atomize (abs (ex / (r * t)))
            insert_ (weight (unsafeProb w))
            backward x ex))
  logBase x y = Lazy
    (liftM2 logBase (forward x) (forward y))
    (\t -> lub_
        (do r <- forward x
            -- TODO if r is 0 or 1 then bot
            w <- atomize (abs ((r ** t) * log r))
            insert_ (weight (unsafeProb w))
            backward y (r ** t))
        (do r <- forward y
            -- TODO if r is 0 or 1 then bot
            let ex = r ** (recip t)
            w <- atomize (abs (ex * (log r) / (t*t)))
            insert_ (weight (unsafeProb w))
            backward x ex))
  sqrt x = Lazy
    (liftM sqrt (forward x))
    (\t -> do u <- atomize (2*t)
              insert_ (ifTrue (less 0 u) . weight (unsafeProb u))
              backward x (t*t))
  sin x = Lazy
    (liftM sin (forward x))
    (\t -> do n <- liftM (Value . fromInt) (lift counting)
              u <- atomize t
              insert_ (ifTrue (and_ [(less (-1) u)
                                    ,(less  u   1)]))
              r1 <- atomize (2*n*pi + asin t)
              r2 <- atomize (2*n*pi + pi - asin t)
              j <- liftM (sqrt_ . unsafeProb) (atomize (1 - t*t))
              r <- lift (superpose [(1, dirac r1), (1, dirac r2)])
              insert_ (weight (recip j))
              backward x (Value r))
  cos x = Lazy
    (liftM cos (forward x))
    (\t -> do n <- liftM (Value . fromInt) (lift counting)
              u <- atomize t
              insert_ (ifTrue (and_ [(less (-1) u)
                                    ,(less  u   1)]))
              r1 <- atomize (2*n*pi + acos t)
              j <- liftM (sqrt_ . unsafeProb) (atomize (1 - t*t))
              r <- lift (superpose [(1, dirac r1)
                                   ,(1, dirac (r1 + pi))])
              insert_ (weight (recip j))
              backward x (Value r))
  tan x = Lazy
    (liftM tan (forward x))
    (\t -> do n <- liftM (Value . fromInt) (lift counting)
              v <- atomize (n*pi + atan t)
              r <- lift (dirac v)
              j <- liftM (recip . unsafeProb) (atomize (1 + t*t))
              insert_ (weight j)
              backward x (Value r))
  asin x = Lazy
    (liftM asin (forward x))
    (\t -> do j <- atomize (cos t)
              insert_ (weight (unsafeProb j))
              backward x (sin t)) -- TODO bounds check for -pi/2 <= t < pi/2
  acos x = Lazy
    (liftM acos (forward x))
    (\t -> do j <- atomize (sin t)
              insert_ (weight (unsafeProb j))
              backward x (cos t))
  atan x = Lazy
    (liftM atan (forward x))
    (\t -> do j <- liftM unsafeProb (atomize (cos t * cos t))
              insert_ (weight (recip j))
              backward x (tan t))
  -- TODO fill in other methods

unpairM :: (Mochastic repr, Lub repr) => Lazy s repr ('HPair a b) ->
           M s repr (Lazy s repr a, Lazy s repr b)
unpairM (Lazy (Return (Pair a b)) _) = Return (a, b)
unpairM ab = do l1 <- gensym
                l2 <- gensym
                store (Unpair l1 l2 ab)
                return (lazyLoc l1, lazyLoc l2)

ifM :: (Mochastic repr, Lub repr) => Lazy s repr 'HBool -> M s repr Bool
ifM (Lazy (Return True_ ) _) = Return True
ifM (Lazy (Return False_) _) = Return False
ifM ab = choice [store (Iftrue  ab) >> return True,
                 store (Iffalse ab) >> return False]

uneitherM :: (Mochastic repr, Lub repr) => Lazy s repr ('HEither a b) ->
             M s repr (Either (Lazy s repr a) (Lazy s repr b))
uneitherM (Lazy (Return (Inl a)) _) = Return (Left  a)
uneitherM (Lazy (Return (Inr a)) _) = Return (Right a)
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
  true              = lazy (return True_)
  false             = lazy (return False_)
  if_ ab t f        = join (liftM (\b -> if b then t else f) (ifM ab))
  vector s f        = lazy (return (Vector s f))
  empty             = scalar0 empty
  size v            = join $ forward v >>= \case
                      Value v' -> return (scalar0 (size v'))
                      Vector s _ -> return s
                      Plate l -> retrieve locateV l $ \case
                        RVLet v' -> do store (VLet l v')
                                       return (scalar0 (size v'))
                        RVBind table rhs -> do store (VBind l table rhs)
                                               return (size rhs)
  index v i         = join $ forward v >>= \case
                      Value v' -> liftM (scalar0 . index v') (evaluate i)
                      Vector _ f -> return (f i)
                      Plate l -> retrieve locateV l $ \case
                        RVLet v' -> do store (VLet l v')
                                       liftM (scalar0 . index v') (evaluate i)
                        RVBind table rhs -> choice
                          $ do sequence_ [ do b <- ifM (equal i j)
                                              if b then reject else return ()
                                         | (j,_) <- table ]
                               x <- forward (index rhs i) >>= memo . unMeasure
                               store (VBind l ((i,x):table) rhs)
                               return x
                          : [ do b <- ifM (equal i j)
                                 if b then do store (VBind l table rhs)
                                              return y
                                      else reject
                            | (j,y) <- table ]
  unsafeProb x = Lazy
    (forward x >>= \case Real  r -> return (Prob r)
                         Value r -> return (Value (unsafeProb r)))
    (\t -> liftM (Value . fromProb) (atomize t) >>= backward x)
  fromProb x = Lazy
    (forward x >>= \case Prob  r -> return (Real r)
                         Value r -> return (Value (fromProb r)))
    (\t -> do u <- atomize t
              insert_ (ifTrue (less 0 u))
              backward x (Value $ unsafeProb u))
  fromInt = scalar1 fromInt
  pi_ = scalar0 pi_
  exp_ x = Lazy
    (liftM (Value . exp_) (evaluate x))
    (\t -> do u <- atomize t
              insert_ (weight (recip u))
              backward x (Value (log_ u)))
  log_ x = Lazy
    (liftM (Value . log_) (evaluate x))
    (\t -> do u <- atomize t
              insert_ (weight (exp_ u))
              backward x (Value (exp_ u)))
  -- TODO fill in other methods
  sqrt_ x = (scalar1 sqrt_ x)
    { backward = (\t -> do u <- atomize (2*t)
                           insert_ (weight u)
                           backward x (t*t)) }
  pow_ x y = (scalar2 pow_ x y)
    { backward = (\t -> lub_
        (do r <- evaluate x
            u <- atomize t
            let w = u * (unsafeProb (abs (log_ r)))
            insert_ (weight (recip w))
            backward y (Value $ log_ u / log_ r))
        (do r <- evaluate y
            u <- atomize t
            let ex = pow_ u (recip r)
                w = abs (fromProb ex / (r * fromProb u))
            insert_ (weight (unsafeProb w))
            backward x (Value ex))) }
  erf = scalar1 erf -- need InvErf to disintegrate Erf
  erf_ = scalar1 erf_ -- need InvErf to disintegrate Erf
  infinity = scalar0 infinity
  negativeInfinity = scalar0 negativeInfinity
  gammaFunc = scalar1 gammaFunc
  betaFunc = scalar2 betaFunc

measure :: (Lub repr) => Lazy s repr a -> Lazy s repr ('HMeasure a)
measure = lazy . return . Measure

unMeasure :: (Mochastic repr, Lub repr) =>
             Hnf s repr ('HMeasure a) -> Lazy s repr a
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
  -- TODO fill in other methods (in particular, categorical and chain)
  -- BUG:
  -- ""Kind incompatibility when matching types:
  -- ""repr1 :: Hakaru * -> *
  -- ""M s repr :: * -> *
  -- ""Expected type: M s repr (Hnf s repr ('HMeasure 'HReal))
  -- ""Actual type: repr1 a0
  uniform lo hi = Lazy (lub_ (forward (scalar2 uniform lo hi))
                             (forward dfault))
                       (backward dfault)
      where dfault = lebesgue `bind` \x ->
                     ifTrue (and_ [less lo x, less x hi])
                     (superpose [(recip (unsafeProb (hi - lo)), dirac x)])
  plate v       = measure $ join $ do l <- gensymVector
                                      store (VBind l [] v)
                                      return (lazy (return (Plate l)))

class Backward (ab :: Hakaru *) (a :: Hakaru *) where
  backward_ :: (Mochastic repr, Lub repr) =>
               Lazy s repr ab -> Lazy s repr a -> M s repr ()

instance Backward a 'HUnit where
  backward_ _ _ = return ()

instance Backward 'HBool 'HBool where
  backward_ a x = ifM (equal_ a x) >>= \b -> if b then return () else reject

instance Backward 'HInt 'HInt where
  backward_ a x = forward x >>= backward a

instance Backward 'HReal 'HReal where
  backward_ a x = forward x >>= backward a

instance Backward 'HProb 'HProb where
  backward_ a x = forward x >>= backward a

instance (Backward a x, Backward b y) =>
         Backward ('HPair a b) ('HPair x y) where
  backward_ ab xy = do (a,b) <- unpairM ab
                       (x,y) <- unpairM xy
                       backward_ a x
                       backward_ b y

instance (Backward a x, Backward b y) =>
         Backward ('HEither a b) ('HEither x y) where
  backward_ ab xy = do a_b <- uneitherM ab
                       x_y <- uneitherM xy
                       case (a_b, x_y) of
                         (Left  a, Left  x) -> backward_ a x
                         (Right b, Right y) -> backward_ b y
                         _                  -> reject

-- TODO: Conditioning on an observed _vector_
   
-- TODO: instance Lambda, instance Integrate, instance Lub

disintegrate
    :: (Mochastic repr, Lub repr, Backward ab a)
    => Lazy s repr a
    -> Lazy s repr ('HMeasure ab)
    -> Lazy s repr ('HMeasure ab)
disintegrate a m =
    measure $ join $ (forward m >>= memo . unMeasure >>= \ab ->
                                     backward_ ab a >> return ab)

type Cond (repr :: Hakaru * -> *) (env :: Hakaru *) (ab :: Hakaru *)
    = forall s t. Lazy s (Compose [] t repr) env
               -> Lazy s (Compose [] t repr) ab

runDisintegrate
    :: (Mochastic repr, Lambda repr, Backward a a)
    => Cond repr env ('HMeasure ('HPair a b))
    -> [repr ('HFun env ('HFun a  ('HMeasure b)))]
runDisintegrate m = runCompose
                  $ lam $ \env ->
                    lam $ \t -> runLazy
                  $ disintegrate (pair (scalar0 t) unit)
                                 (m (scalar0 env))
                    `bind` dirac . snd_

density
    :: (Mochastic repr, Lambda repr, Integrate repr, Backward a a)
    => Cond (Expect repr) env ('HMeasure a)
    -> [repr (Expect' env) -> repr (Expect' a) -> repr 'HProb]
density m = [ \env t -> total (d `app` Expect env `app` Expect t)
            | d <- runCompose
                 $ lam $ \env ->
                   lam $ \t -> runLazy
                 $ disintegrate' (scalar0 t)
                                 (m (scalar0 env)) ]
  where disintegrate'
            :: (Mochastic repr, Lub repr, Backward a a)
            => Lazy s repr a
            -> Lazy s repr ('HMeasure a)
            -> Lazy s repr ('HMeasure a)
        disintegrate' = disintegrate

observe :: (Mochastic repr, Lambda repr, Backward a a) =>
           (forall s t.
            ( Lazy s (Compose [] t repr) a
            , (Lazy s (Compose [] t repr) env
              -> Lazy s (Compose [] t repr) ('HMeasure ('HPair a b))) ))
        -> [repr ('HFun env ('HMeasure b))]
observe tm = runCompose
             $ lam $ \env -> runLazy
             $ let (t,m) = tm
               in disintegrate (pair t unit)
                               (m (scalar0 env))
                  `bind` dirac . snd_

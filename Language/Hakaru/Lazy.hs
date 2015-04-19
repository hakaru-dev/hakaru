{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts, FlexibleInstances,
             Rank2Types, GADTs, KindSignatures, LambdaCase #-}
{-# OPTIONS -Wall #-}

module Language.Hakaru.Lazy (Lazy, runLazy, Backward, disintegrate,
       Cond, runDisintegrate, density,
       scalar0, lazy) where

import Prelude hiding (Real)
import Language.Hakaru.Syntax (Real, Prob, Measure, Vector,
       Number, Fraction(..), EqType(Refl), Order(..), Base(..), snd_, equal_,
       Mochastic(..), weight, Integrate(..), Lambda(..), Lub(..))
import Language.Hakaru.Compose
import Control.Monad (liftM, liftM2)
import Data.Maybe (isNothing)
import Unsafe.Coerce (unsafeCoerce)
import Language.Hakaru.Expect (Expect(Expect), Expect', total)

ifTrue, ifFalse :: (Mochastic repr) => repr Bool ->
                   repr (Measure w) -> repr (Measure w)
ifTrue  x m = if_ x m (superpose [])
ifFalse x m = if_ x (superpose []) m

uninl :: (Mochastic repr) => repr (Either a b) ->
         (repr a -> repr (Measure w)) -> repr (Measure w)
uninl x c = uneither x c (\_ -> superpose [])

uninr :: (Mochastic repr) => repr (Either a b) ->
         (repr b -> repr (Measure w)) -> repr (Measure w)
uninr x c = uneither x (\_ -> superpose []) c

data M s repr a
  = Return a
  | M (forall w. (a -> Heap s repr -> repr (Measure w))
                    -> Heap s repr -> repr (Measure w))

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

data Lazy s (repr :: * -> *) a = Lazy
  { forward  :: M s repr (Hnf s repr a)
  , backward :: (Number a) => repr a -> M s repr () }

lazy :: (Lub repr) => M s repr (Hnf s repr a) -> Lazy s repr a
lazy m = Lazy m (const bot)

join :: M s repr (Lazy s repr a) -> Lazy s repr a
join m = Lazy (m >>= forward) (\t -> m >>= (`backward` t))

instance (Lub repr) => Lub (Lazy s repr) where
  bot = Lazy bot (const bot)
  lub (Lazy f1 b1) (Lazy f2 b2) = Lazy (lub f1 f2) (\t -> lub (b1 t) (b2 t))

data Hnf s (repr :: * -> *) a where
  Pair    :: Lazy s repr a -> Lazy s repr b ->     Hnf s repr (a,b)
  True_   ::                                       Hnf s repr Bool
  False_  ::                                       Hnf s repr Bool
  Inl     :: Lazy s repr a ->                      Hnf s repr (Either a b)
  Inr     :: Lazy s repr b ->                      Hnf s repr (Either a b)
  Int     :: Integer ->                            Hnf s repr Int
  Real    :: Rational ->  {-constant propagation-} Hnf s repr Real
  Prob    :: Rational ->  {-constant propagation-} Hnf s repr Prob
  Value   :: repr a ->                             Hnf s repr a
  Measure :: Lazy s repr a ->                      Hnf s repr (Measure a)
  Vector  :: Lazy s repr Int ->
             (Lazy s repr Int -> Lazy s repr a) -> Hnf s repr (Vector a)
  Plate   :: Loc (Vector s) a ->                   Hnf s repr (Vector a)

determine :: (Lub repr) => Lazy s repr a -> M s repr (Hnf s repr a)
determine z = forward z >>= \case
  Pair x y     -> liftM2 Pair (liftM (lazy . return) (determine x))
                              (liftM (lazy . return) (determine y))
  Inl x        -> liftM (Inl . lazy . return) (determine x)
  Inr y        -> liftM (Inr . lazy . return) (determine y)
  Vector s f   -> liftM (\s' -> Vector (lazy (return s')) f) (determine s)
  w            -> return w

atomize :: (Mochastic repr, Lub repr) =>
           Hnf s repr a -> M s repr (repr a)
atomize = \case
  Pair x y     -> liftM2 pair (evaluate x) (evaluate y)
  True_        -> return true
  False_       -> return false
  Inl x        -> liftM inl (evaluate x)
  Inr y        -> liftM inr (evaluate y)
  Int n        -> return (fromInteger n)
  Real r       -> return (fromRational r)
  Prob r       -> return (fromRational r)
  Value a      -> return a
  Measure x    -> liftM (evaluateMeasure x) duplicateHeap
  Vector s f   -> evaluateVector s [] f
  Plate l      -> let process (RVLet v)          = return v
                      process (RVBind table rhs) = evaluatePlate table rhs
                  in retrieve locateV l (\retrieval -> do v <- process retrieval
                                                          store (VLet l v)
                                                          return v)      

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
                   Lazy s repr a -> Heap s repr -> repr (Measure a)
-- Call duplicateHeap before evaluateMeasure!
evaluateMeasure z = unM (do a <- evaluate z
                            determineHeap
                            return (dirac a))
                        const

evaluateVector :: (Mochastic repr, Lub repr) =>
                  Lazy s repr Int ->
                  [(Lazy s repr Int, Lazy s repr a)] ->
                  (Lazy s repr Int -> Lazy s repr a) ->
                  M s repr (repr (Vector a))
evaluateVector s table f = do
  s' <- evaluate s
  table' <- evaluatePairs table
  heap <- duplicateHeap
  let g i = evaluateMeasure (f (scalar0 i)) heap
  lift (plate (vector s' (override table' g)))

evaluatePlate :: (Mochastic repr, Lub repr) =>
                 [(Lazy s repr Int, Lazy s repr a)] ->
                 Lazy s repr (Vector (Measure a)) ->
                 M s repr (repr (Vector a))
evaluatePlate table rhs = do
  size'  <- evaluate (size rhs)
  table' <- evaluatePairs table
  vm <- evaluate rhs
  lift (plate (vector size' (override table' (index vm))))

evaluatePairs :: (Mochastic repr, Lub repr) =>
                 [(Lazy s repr a, Lazy s repr b)] -> M s repr [(repr a, repr b)]
evaluatePairs = mapM (\(a,b) -> liftM2 (,) (evaluate a) (evaluate b))

override :: (Mochastic repr) => [(repr Int, repr a)] ->
            (repr Int -> repr (Measure a)) -> (repr Int -> repr (Measure a))
override table f = foldr (\(j,y) c i -> if_ (equal i j) (dirac y) (c i)) f table

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

gensymVector :: M s repr (Loc (Vector s) a)
gensymVector = M (\c h@Heap{fresh=f} -> c (Loc f) h{fresh = succ f})

data Binding s repr where
  Bind    :: Loc s a ->              Lazy s repr a            -> Binding s repr
  Let     :: Loc s a ->              Hnf s repr a             -> Binding s repr
  Unpair  :: Loc s a -> Loc s b ->   Lazy s repr (a,b)        -> Binding s repr
  Iftrue  ::                         Lazy s repr Bool         -> Binding s repr
  Iffalse ::                         Lazy s repr Bool         -> Binding s repr
  Uninl   :: Loc s a ->              Lazy s repr (Either a b) -> Binding s repr
  Uninr   :: Loc s b ->              Lazy s repr (Either a b) -> Binding s repr
  Weight  ::                         Lazy s repr Prob         -> Binding s repr
  VBind   :: Loc (Vector s) a -> [(Lazy s repr Int, Lazy s repr a)] ->
                             Lazy s repr (Vector (Measure a)) -> Binding s repr
  VLet    :: Loc (Vector s) a -> repr (Vector a)              -> Binding s repr

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
      Weight        rhs -> do x <- evaluate rhs
                              insert_ (weight x)
                              return []
      VBind l table rhs -> do v <- evaluatePlate table rhs
                              return [VLet l v]
      Let    _      _   -> return [entry]
      Unpair _ _    _   -> return [entry]
      VLet   _      _   -> return [entry]

data Retrieval s repr a where
  RBind  :: Lazy s repr a ->                    Retrieval s repr a
  RLet   :: Hnf s repr a ->                     Retrieval s repr a
  RFst   :: Loc s b -> Lazy s repr (a,b) ->     Retrieval s repr a
  RSnd   :: Loc s a -> Lazy s repr (a,b) ->     Retrieval s repr b
  RInl   :: Lazy s repr (Either a b) ->         Retrieval s repr a
  RInr   :: Lazy s repr (Either a b) ->         Retrieval s repr b

data VRetrieval s repr a where
  RVBind :: [(Lazy s repr Int, Lazy s repr a)] ->
            Lazy s repr (Vector (Measure a)) -> VRetrieval s repr a
  RVLet  :: repr (Vector a)                  -> VRetrieval s repr a

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

locateV :: Loc (Vector s) a -> Binding s repr -> Maybe (VRetrieval s repr a)
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

bwdLoc :: (Mochastic repr, Lub repr, Number a) => Loc s a -> repr a -> M s repr ()
bwdLoc l t = retrieve locate l (\retrieval -> do process retrieval
                                                 update l (Value t))
  where
    process (RBind   rhs) = backward rhs t
    process (RLet    _  ) = bot
    process (RFst l2 rhs) = forward rhs >>= \case
                            Pair a b -> store (Bind l2 b) >> backward a t
                            Value _  -> bot
    process (RSnd l1 rhs) = forward rhs >>= \case
                            Pair a b -> store (Bind l1 a) >> backward b t
                            Value _  -> bot
    process (RInl    rhs) = forward rhs >>= \case
                            Inl a    -> backward a t
                            Inr _    -> reject
                            Value _  -> bot
    process (RInr    rhs) = forward rhs >>= \case
                            Inr b    -> backward b t
                            Inl _    -> reject
                            Value _  -> bot

scalar0 :: (Lub repr) => repr a -> Lazy s repr a
scalar0 op = lazy (return (Value op))

scalar1 :: (Lub repr, Mochastic repr) => (repr a -> repr b) ->
           Lazy s repr a -> Lazy s repr b
scalar1 op m = lazy (liftM (Value . op) (evaluate m))

scalar2 :: (Lub repr, Mochastic repr) => (repr a -> repr b -> repr c) ->
           Lazy s repr a -> Lazy s repr b -> Lazy s repr c
scalar2 op m n = lazy (liftM2 ((Value.) . op) (evaluate m) (evaluate n))

comparison :: (Lub repr, Mochastic repr) =>
              (Integer -> Integer -> Bool) ->
              (repr a -> repr a -> repr Bool) ->
              Lazy s repr a -> Lazy s repr a -> Lazy s repr Bool
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

isNum :: (Number a) => Rational -> Hnf s repr a -> Bool
isNum m = \case
  Int n  -> fromInteger n == m
  Real n -> n == m
  Prob n -> n == m
  _      -> False

atom1 :: (Mochastic repr, Lub repr) => (repr a -> repr b) ->
         Hnf s repr a -> M s repr (Hnf s repr b)
atom1 op a = liftM (Value . op) (atomize a)

atom2 :: (Mochastic repr, Lub repr) => (repr a -> repr b -> repr c) ->
         Hnf s repr a -> Hnf s repr b -> M s repr (Hnf s repr c)
atom2 op a b = liftM2 ((Value .) . op) (atomize a) (atomize b)

add :: (Mochastic repr, Lub repr, Num (repr a), Number a) => 
       Lazy s repr a -> Lazy s repr a -> Lazy s repr a
add x y = Lazy
          (do fx <- forward x
              fy <- forward y
              case (fx,fy) of
                (Int a,  Int b)  -> return (Int (a+b))
                (Real a, Real b) -> return (Real (a+b))
                (Prob a, Prob b) -> return (Prob (a+b))
                (Value _, s) | isNum 0 s -> return fx
                (s, Value _) | isNum 0 s -> return fy
                _ -> atom2 (+) fx fy)
          (\t -> lub (evaluate x >>= \r -> backward y (t - r))
                     (evaluate y >>= \r -> backward x (t - r)))

sub :: (Mochastic repr, Lub repr, Num (repr a), Number a) => 
       Lazy s repr a -> Lazy s repr a -> Lazy s repr a
sub x y = Lazy
          (do fx <- forward x
              fy <- forward y
              case (fx,fy) of                
                (Int a,  Int b)  -> return (Int (a-b))
                (Real a, Real b) -> return (Real (a-b))
                (Prob a, Prob b) -> return (Prob (a-b))
                (Value _, s) | isNum 0 s -> return fx
                (s, Value _) | isNum 0 s -> return fy
                _ -> atom2 (-) fx fy)
          (\t -> lub (evaluate x >>= \r -> backward y (r - t))
                     (evaluate y >>= \r -> backward x (r + t)))

mul :: (Mochastic repr, Lub repr, Num (repr a), Number a) => 
       Lazy s repr a -> Lazy s repr a -> Lazy s repr a
mul x y = lazy
          (do fx <- forward x
              fy <- forward y
              case (fx,fy) of
                (Int a,  Int b)  -> return (Int (a*b))
                (Real a, Real b) -> return (Real (a*b))
                (Prob a, Prob b) -> return (Prob (a*b))
                (Value _, s) | isNum 0 s -> return s
                             | isNum 1 s  -> return fx
                (s, Value _) | isNum 0 s -> return s
                             | isNum 1 s  -> return fy
                _ -> atom2 (*) fx fy)
          
neg :: (Mochastic repr, Lub repr, Num (repr a), Number a) =>
       Lazy s repr a -> Lazy s repr a
neg x = Lazy
        (do fx <- forward x
            case fx of
              Int a  -> return (Int (negate a))
              Real a -> return (Real (negate a))
              Prob a -> return (Prob (negate a))
              _      -> atom1 negate fx)
        (\t -> backward x (negate t))

abz :: (Mochastic repr, Lub repr, Num (repr a), Order repr a) =>
       Lazy s repr a -> Lazy s repr a
abz x = Lazy
        (do fx <- forward x
            case fx of
              Int a  -> return (Int (abs a))
              Real a -> return (Real (abs a))
              Prob a -> return (Prob (abs a))
              _      -> atom1 abs fx)
        (\t -> lift (if_ (less 0 t) (superpose [(1, dirac t), (1, dirac (-t))])
                                    (ifTrue (equal 0 t) (dirac 0)))
               >>= backward x)

sign :: (Mochastic repr, Lub repr, Num (repr a), Number a) =>
        Lazy s repr a -> Lazy s repr a
sign x = lazy
         (do fx <- forward x
             case fx of
               Int a  -> return (Int (signum a))
               Real a -> return (Real (signum a))
               Prob a -> return (Prob (signum a))
               _      -> atom1 signum fx)
 
inv :: (Mochastic repr, Lub repr, Fractional (repr a), Fraction a) =>
       Lazy s repr a -> Lazy s repr a
inv x = Lazy
        (do fx <- forward x
            case fx of
              Real a -> return (Real (recip a))
              Prob a -> return (Prob (recip a))
              _      -> atom1 recip fx)
        (\t -> do insert_ (weight (recip (unsafeProbFraction (t * t))))
                  backward x (recip t))

instance (Mochastic repr, Lub repr) => Num (Lazy s repr Int) where
  (+) = add
  (-) = sub
  x * y = (mul x y)
    { backward = (\t ->
        lub (do r <- evaluate x
                n <- lift counting
                insert_ (ifTrue (equal (r * n) t))
                backward y n)
            (do r <- evaluate y
                n <- lift counting
                insert_ (ifTrue (equal (n * r) t))
                backward x n)) }
  negate = neg
  abs = abz
  signum x = (sign x)
             { backward = (\t -> do n <- lift counting
                                    insert_ (ifTrue (equal (signum n) t))
                                    backward x n) }
  fromInteger n = Lazy (return (Int n))
                       (\t -> insert_ (ifTrue (equal (fromInteger n) t)))

instance (Mochastic repr, Lub repr) => Num (Lazy s repr Real) where
  (+) = add
  (-) = sub
  x * y = (mul x y)
    { backward = (\t ->
        lub (do r <- evaluate x
                insert_ (weight (recip (unsafeProbFraction (abs r))))
                backward y (t / r))
            (do r <- evaluate y
                insert_ (weight (recip (unsafeProbFraction (abs r))))
                backward x (t / r))) }
  negate = neg
  abs = abz
  signum = sign
  fromInteger n = lazy (return (Real (fromInteger n)))

instance (Mochastic repr, Lub repr) => Num (Lazy s repr Prob) where
  (+) = add  
  (-) = sub
  x * y = (mul x y)
    { backward = (\t ->
        lub (do r <- evaluate x
                insert_ (weight (recip (unsafeProbFraction (abs r))))
                backward y (t / r))
            (do r <- evaluate y
                insert_ (weight (recip (unsafeProbFraction (abs r))))
                backward x (t / r))) }
  negate = neg
  abs = abz
  signum = sign
  fromInteger n = lazy (return (Prob (fromInteger n)))

instance (Mochastic repr, Lub repr) =>
         Fractional (Lazy s repr Real) where
  recip = inv
  fromRational r = lazy (return (Real r))                   
  -- TODO fill in (/)

instance (Mochastic repr, Lub repr) =>
         Fractional (Lazy s repr Prob) where
  recip = inv
  fromRational r = lazy (return (Prob r))
  -- TODO fill in (/)

instance (Mochastic repr, Lub repr) =>
         Floating (Lazy s repr Real) where
  pi = scalar0 pi
  exp x = Lazy
    (liftM (Value . exp) (evaluate x))
    (\t -> do insert_ (ifTrue (less 0 t) . weight (recip (unsafeProb t)))
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
    (liftM (Value . unsafeProb) (evaluate x))
    (\t -> backward x (fromProb t))
  fromProb x = Lazy
    (liftM (Value . fromProb) (evaluate x))
    (\t -> do insert_ (ifTrue (less 0 t))
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
             Hnf s repr (Measure a) -> Lazy s repr a
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
  plate v       = measure $ join $ do l <- gensymVector
                                      store (VBind l [] v)
                                      return (lazy (return (Plate l)))

class Backward ab a where
  backward_ :: (Mochastic repr, Lub repr) =>
               Lazy s repr ab -> Lazy s repr a -> M s repr ()

instance Backward a () where
  backward_ _ _ = return ()

instance Backward Bool Bool where
  backward_ a x = ifM (equal_ a x) >>= \b -> if b then return () else reject

instance Backward Int Int where
  backward_ a x = evaluate x >>= backward a

instance Backward Real Real where
  backward_ a x = evaluate x >>= backward a

instance Backward Prob Prob where
  backward_ a x = evaluate x >>= backward a

instance (Backward a x, Backward b y) =>
         Backward (a,b) (x,y) where
  backward_ ab xy = do (a,b) <- unpairM ab
                       (x,y) <- unpairM xy
                       backward_ a x
                       backward_ b y

instance (Backward a x, Backward b y) =>
         Backward (Either a b) (Either x y) where
  backward_ ab xy = do a_b <- uneitherM ab
                       x_y <- uneitherM xy
                       case (a_b, x_y) of
                         (Left  a, Left  x) -> backward_ a x
                         (Right b, Right y) -> backward_ b y
                         _                  -> reject

-- TODO: Conditioning on an observed _vector_
   
-- TODO: instance Lambda, instance Integrate, instance Lub

disintegrate :: (Mochastic repr, Lub repr, Backward ab a) =>
                Lazy s repr a ->
                Lazy s repr (Measure ab) -> Lazy s repr (Measure ab)
disintegrate a m = measure $ join $ (forward m >>= memo . unMeasure >>= \ab ->
                                     backward_ ab a >> return ab)

type Cond repr env ab = forall s t. Lazy s (Compose [] t repr) env
                                 -> Lazy s (Compose [] t repr) ab

runDisintegrate :: (Mochastic repr, Lambda repr, Backward a a) =>
                   Cond repr env (Measure (a,b)) ->
                   [repr (env -> a -> Measure b)]
runDisintegrate m = runCompose
                  $ lam $ \env ->
                    lam $ \t -> runLazy
                  $ disintegrate (pair (scalar0 t) unit)
                                 (m (scalar0 env))
                    `bind` dirac . snd_

density :: (Mochastic repr, Lambda repr, Integrate repr, Backward a a) =>
           Cond (Expect repr) env (Measure a) ->
           [repr (Expect' env) -> repr (Expect' a) -> repr Prob]
density m = [ \env t -> total (d `app` Expect env `app` Expect t)
            | d <- runCompose
                 $ lam $ \env ->
                   lam $ \t -> runLazy
                 $ disintegrate' (scalar0 t)
                                 (m (scalar0 env)) ]
  where disintegrate' :: (Mochastic repr, Lub repr, Backward a a) =>
                         Lazy s repr a ->
                         Lazy s repr (Measure a) -> Lazy s repr (Measure a)
        disintegrate' = disintegrate

{-# LANGUAGE RankNTypes, NoMonomorphismRestriction, BangPatterns,
  DeriveDataTypeable, GADTs, ScopedTypeVariables,
  ExistentialQuantification, StandaloneDeriving #-}

module InterpreterMH where

import System.Random (RandomGen, StdGen, randomR, getStdGen)
import System.IO

import Control.Monad
import Data.Dynamic
import Data.Function (on)
import Data.Maybe

import qualified Data.Map.Strict as M

import RandomChoice (marsaglia, lnFact, poisson_rng)
import Visual

{-

Shortcomings of this implementation

* uses parent-conditional sampling for proposal distribution
* re-evaluates entire program at every sample
* lacks way to block sample groups of variables

-}

type DistVal = Dynamic

data Dist a = Dist {logDensity :: a -> Likelihood,
                    sample :: forall g. RandomGen g => g -> (a, g)}
deriving instance Typeable1 Dist
 
data XRP = forall e. Typeable e => XRP (e, Dist e)

unXRP :: Typeable a => XRP -> Maybe (a, Dist a)
unXRP (XRP (e,f)) = cast (e,f)

type Var a = Int

type Likelihood = Double
type Visited = Bool
type Observed = Bool
type Cond = Maybe DistVal

type Subloc = Int
type Name = [Subloc]
type Database = M.Map Name (XRP, Likelihood, Visited, Observed)
newtype Measure a = Measure {unMeasure :: (RandomGen g) =>
                              (Name
                              ,Database
                              ,(Likelihood, Likelihood)
                              ,[Cond]
                              ,g
                           ) -> (a
                                ,Database
                                ,(Likelihood, Likelihood)
                                ,[Cond]
                                ,g)}
  deriving (Typeable)

-- n  is structural_name
-- d  is database
-- ll is likelihood of expression
-- conds is the observed data
-- g  is the random seed


lit :: (Eq a, Typeable a) => a -> a
lit = id

return_ :: a -> Measure a
return_ x = Measure (\ (n, d, l, conds, g) -> (x, d, l, conds, g))

makeXRP :: (Typeable a, RandomGen g) => Cond -> Dist a
        -> Name -> Database -> g
        -> (a, Database, Likelihood, Likelihood, g)
makeXRP obs dist' n db g =
    case M.lookup n db of
      Just (xd, lb, b, ob) ->
        let Just (xb, dist) = unXRP xd
            (x,l) = case obs of
                      Just xd ->
                          let Just x = fromDynamic xd
                          in (x, logDensity dist x)
                      Nothing -> (xb, lb)
            l' = logDensity dist' x
            d1 = M.insert n (XRP (x,dist),
                             l',
                             True,
                             ob) db
        in (x, d1, l', 0, g)
      Nothing ->
        let (xnew, l, g1) = case obs of
             Just xdnew ->
                 let Just xnew = fromDynamic xdnew
                 in (xnew, logDensity dist' xnew, g)
             Nothing ->
                 (xnew, logDensity dist' xnew, g1)
                where (xnew, g1) = sample dist' g
            d1 = M.insert n (XRP (xnew, dist'),
                             l,
                             True,
                             isJust obs) db
        in (xnew, d1, l, l, g1)

updateLikelihood :: (Typeable a, RandomGen g) => 
                    Likelihood -> Likelihood ->
                    (a, Database, Likelihood, Likelihood, g) ->
                    [Cond] ->
                    (a, Database, (Likelihood, Likelihood), [Cond], g)
updateLikelihood llTotal llFresh (x,d,l,lf,g) conds =
    (x, d, (llTotal+l, llFresh+lf), conds, g)

dirac :: (Eq a, Typeable a) => a -> Cond -> Measure a
dirac theta obs = Measure $ \(n, d, (llTotal,llFresh), conds, g) ->
    let dist' = Dist {logDensity = (\ x -> if x == theta then 0 else log 0),
                      sample = (\ g -> (theta,g))}
        xrp = makeXRP obs dist' n d g
    in updateLikelihood llTotal llFresh xrp conds

bern :: Double -> Cond -> Measure Bool
bern p obs = Measure $ \(n, d, (llTotal, llFresh), conds, g) ->
    let dist' = Dist {logDensity = (\ x -> log (if x then p else 1 - p)),
                      sample = (\ g -> case randomR (0, 1) g of
                                         (t, g') -> (t <= p, g'))}
        xrp = makeXRP obs dist' n d g
    in updateLikelihood llTotal llFresh xrp conds

poisson :: Double -> Cond -> Measure Int
poisson l obs = Measure $ \(n, d, (llTotal, llFresh), conds, g) ->
    let poissonLogDensity l x | l > 0 && x> 0 = (fromIntegral x)*(log l) - lnFact x - l
        poissonLogDensity l x | x==0 = -l
        poissonLogDensity _ _ = log 0
        dist' = Dist {logDensity = poissonLogDensity l,
                      sample = poisson_rng l}
        xrp = makeXRP obs dist' n d g
    in updateLikelihood llTotal llFresh xrp conds

uniform :: Double -> Double -> Cond -> Measure Double
uniform lo hi obs = Measure $ \(n, d, (llTotal,llFresh), conds, g) ->
    let uniformLogDensity lo hi x | lo <= x && x <= hi = log (recip (hi - lo))
        uniformLogDensity _ _  x = log 0
        dist' = Dist {logDensity = uniformLogDensity lo hi,
                      sample = (\ g -> randomR (lo, hi) g)}
        xrp = makeXRP obs dist' n d g
    in updateLikelihood llTotal llFresh xrp conds

normal :: Double -> Double -> Cond -> Measure Double
normal mu sd obs = Measure $ \(n, d, (llTotal, llFresh), conds, g) ->
    let normalLogDensity x = (-tau * square (x - mu) +
                              log (tau / pi / 2)) / 2
        square y = y * y
        tau = 1 / square sd
        dist' = Dist {logDensity = normalLogDensity,
                      sample = (\ g -> case marsaglia g of
                                         ((x, _), g1) -> (mu + sd * x, g1))}
        xrp = makeXRP obs dist' n d g
    in updateLikelihood llTotal llFresh xrp conds

categorical :: (Eq a, Typeable a) => [(a,Double)] 
            -> Cond -> Measure a
categorical list obs = Measure $ \(n, d, (llTotal, llFresh), conds, g) ->
    let categoricalLogDensity list x = log $ fromMaybe 0 (lookup x list)
        categoricalSample list g = (elem, g1)
           where
             (p, g1) = randomR (0, total) g
             elem = fst $ head $ filter (\(_,p0) -> p <= p0) sumList
             sumList = scanl1 (\acc (a, b) -> (a, b + snd(acc))) list
             total = sum $ map snd list
        dist' = Dist {logDensity = categoricalLogDensity list,
                      sample = categoricalSample list}
        xrp = makeXRP obs dist' n d g
    in updateLikelihood llTotal llFresh xrp conds

factor :: Likelihood -> Measure ()
factor l = Measure $ \(n, d, (llTotal, llFresh), conds, g) ->
   ((), d, (llTotal + l, llFresh), conds, g)

resample :: RandomGen g => XRP -> g ->
            (XRP, Likelihood, Likelihood, Likelihood, g)
resample (XRP (x, dist)) g =
    let (x', g1) = sample dist g
        fwd = logDensity dist x'
        rvs = logDensity dist x
        l' = fwd
    in (XRP (x', dist), l', fwd, rvs, g1)

bind :: Measure a -> (a -> Measure b) -> Measure b
bind (Measure m) cont = Measure $ \ (n,d,ll,conds,g) ->
    let (v, d1, ll1, conds1, g1) = m (0:n, d, ll, conds, g)
    in unMeasure (cont v) (1:n, d1, ll1, conds1, g1)

conditioned :: (Cond -> Measure a) -> Measure a
conditioned f = Measure $ \ (n,d,ll,cond:conds,g) ->
    unMeasure (f cond) (n, d, ll, conds, g)

unconditioned :: (Cond -> Measure a) -> Measure a
unconditioned f = f Nothing

instance Monad Measure where
  return = return_
  (>>=)    = bind

lam :: (a -> b) -> (a -> b)
lam f = f

app :: (a -> b) -> a -> b
app f x = f x

fix :: ((a -> b) -> (a -> b)) -> (a -> b)
fix g = f where f = g f

ifThenElse :: Bool -> a -> a -> a
ifThenElse True  t _ = t
ifThenElse False _ f = f

run :: Measure a -> [Cond] -> IO (a, Database, Likelihood)
run (Measure prog) conds = do
  g <- getStdGen
  let (v, d, ll, conds1, g') =
          prog ([0], M.empty, (0,0), conds, g)
  return (v, d, fst ll)

traceUpdate :: RandomGen g => Measure a -> Database -> [Cond] -> g
            -> (a, Database, Likelihood, Likelihood, Likelihood, g)
traceUpdate (Measure prog) d conds g = do
  let d1 = M.map (\ (x, l, _, ob) -> (x, l, False, ob)) d
  let (v, d2, (llTotal, llFresh), conds1, g1) =
          prog ([0], d1, (0,0), conds, g)
  let (d3, stale_d) = M.partition (\ (_, _, v, _) -> v) d2
  let llStale = M.foldl' (\ llStale (_,l,_,_) -> llStale + l)
                0 stale_d
  (v, d3, llTotal, llFresh, llStale, g1)

initialStep :: Measure a -> [Cond] ->
               IO (a, Database,
                   Likelihood, Likelihood, Likelihood, StdGen)
initialStep prog conds = do
  g <- getStdGen
  return $ traceUpdate prog M.empty conds g

-- TODO: Make a way of passing user-provided proposal distributions
updateDB :: (RandomGen g) => 
            Name -> Database -> Observed -> XRP -> g
         -> (Database, Likelihood, Likelihood, Likelihood, g)
updateDB name db ob xd g = (db', l', fwd, rvs, g)
    where db' = M.insert name (x', l', True, ob) db
          (x', l', fwd, rvs, g1) = resample xd g

transition :: (Typeable a, RandomGen g) => Measure a -> [Cond]
           -> a -> Database -> Likelihood -> g -> [a]
transition prog conds v db ll g =
  let dbSize = M.size db
      -- choose an unconditioned choice
      (condDb, uncondDb) = M.partition (\ (_, _, _, ob) -> ob) db
      (choice, g1) = randomR (0, (M.size uncondDb) -1) g
      (name, (xd, l, _, ob))  = M.elemAt choice uncondDb
      (db', l', fwd, rvs, g2) = updateDB name db ob xd g1
      (v', db2, llTotal, llFresh, llStale, g3) = traceUpdate prog db' conds g2
      a = llTotal - ll
          + rvs - fwd
          + log (fromIntegral dbSize) - log (fromIntegral $ M.size db2)
          + llStale - llFresh
      (u, g4) = randomR (0 :: Double, 1) g3 in

  if (log u < a) then
      v' : (transition prog conds v' db2 llTotal g4)
  else
      v : (transition prog conds v db ll g4)

mcmc :: Typeable a => Measure a -> [Cond] -> IO [a]
mcmc prog conds = do
  (v, d, llTotal, llFresh, llStale, g) <- initialStep prog conds
  return $ transition prog conds v d llTotal g

test :: Measure Bool
test = unconditioned (bern (lit (0.5 :: Double))) `bind`
       \c ->  ifThenElse c (conditioned
                            (normal (lit (1 :: Double))
                                    (lit (1 :: Double))))
                           (conditioned
                            (uniform (lit (0 :: Double))
                                     (lit (3 :: Double)))) `bind`
              \_ -> return_ c

main_run_test :: IO (Bool, Database, Likelihood)
main_run_test = run test [Just (toDyn (-2 :: Double))]

main_test :: IO [Bool]
main_test = mcmc test [Just (toDyn (-2 :: Double))]

test_two_normals = unconditioned (bern 0.5) `bind` \coin ->
       ifThenElse coin (conditioned (normal 0 1))
                       (conditioned (normal 100 1)) `bind` \_ ->
       return_ coin

main_test2 :: IO [Bool]
main_test2 = mcmc test_two_normals [Just (toDyn (1 :: Double))]

main :: IO ()
main = do
  l <- mcmc (unconditioned
             (normal
              (lit (1.0 :: Double))
              (lit (3.0 :: Double))) `bind` \n ->
             return_ n) [] :: IO [Double]
  viz 10000 ["normal"] (map (\ x -> [x]) l)

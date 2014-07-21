{-# LANGUAGE RankNTypes, NoMonomorphismRestriction, BangPatterns,
  DeriveDataTypeable, GADTs, ScopedTypeVariables,
  ExistentialQuantification, StandaloneDeriving #-}
{-# OPTIONS -Wall #-}

module InterpreterMH where

import System.Random (RandomGen, StdGen, randomR, getStdGen)

import Data.Dynamic
import Data.Maybe

import qualified Data.Map.Strict as M

import Lambda
import RandomChoice
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
 
-- and what does XRP stand for?
data XRP where
  XRP :: Typeable e => (e, Dist e) -> XRP

unXRP :: Typeable a => XRP -> Maybe (a, Dist a)
unXRP (XRP (e,f)) = cast (e,f)

type Likelihood = Double
type Visited = Bool
type Observed = Bool
type Cond = Maybe DistVal

type Subloc = Int
type Name = [Subloc]
data DBEntry = DBEntry {
      xrp  :: XRP, 
      llhd :: Likelihood, 
      vis  :: Visited,
      observed :: Observed }
type Database = M.Map Name DBEntry

data SamplerState g where
  S :: { ldb :: Database, -- ldb = local database
         -- (total likelihood, total likelihood of XRPs newly introduced)
         llh2 :: {-# UNPACK #-} !(Likelihood, Likelihood),
         cnds :: [Cond], -- conditions left to process
         seed :: g } -> SamplerState g

type Sampler a = forall g. (RandomGen g) => SamplerState g -> (a, SamplerState g)
newtype CSampler a = CSampler (Name -> Cond -> Sampler a)

sreturn :: a -> Sampler a
sreturn x s = (x, s)

sbind :: Sampler a -> (a -> Sampler b) -> Sampler b
sbind s k = \ st -> let (v, s') = s st in k v s'

smap :: (a -> b) -> Sampler a -> Sampler b
smap f s = sbind s (\a -> sreturn (f a))

newtype Measure a = Measure {unMeasure :: Name -> Sampler a }
  deriving (Typeable)

return_ :: a -> Measure a
return_ x = Measure $ \ _ -> sreturn x

updateXRP :: Typeable a => Name -> Cond -> Dist a -> Sampler a
updateXRP n obs dist' s@(S {ldb = db, seed = g}) =
    case M.lookup n db of
      Just (DBEntry xd lb _ ob) ->
        let Just (xb, dist) = unXRP xd
            (x,_) = case obs of
                      Just yd ->
                          let Just y = fromDynamic yd
                          in (y, logDensity dist y)
                      Nothing -> (xb, lb)
            l' = logDensity dist' x
            d1 = M.insert n (DBEntry (XRP (x,dist)) l' True ob) db
        in (x, s {ldb = d1,
                  llh2 = updateLikelihood l' 0 s,
                  seed = g})
      Nothing ->
        let (xnew2, l, g2) = case obs of
             Just xdnew ->
                 let Just xnew = fromDynamic xdnew
                 in (xnew, logDensity dist' xnew, g)
             Nothing ->
                 let (xnew, g1) = sample dist' g
                 in (xnew, logDensity dist' xnew, g1)
            d1 = M.insert n (DBEntry (XRP (xnew2, dist')) l True (isJust obs)) db
        in (xnew2, s {ldb = d1,
                      llh2 = updateLikelihood l l s,
                      seed = g2})

updateLikelihood :: RandomGen g => 
                    Likelihood -> Likelihood -> SamplerState g ->
                    (Likelihood, Likelihood)
updateLikelihood llTotal llFresh s =
  let (l,lf) = llh2 s in (llTotal+l, llFresh+lf)

dirac :: (Eq a, Typeable a) => a -> CSampler a
dirac theta = CSampler $ \ name obs ->
    let dist' = Dist {logDensity = (\ x -> if x == theta then 0 else log 0),
                      sample = (\ g -> (theta,g))}
    in updateXRP name obs dist'

bern :: Double -> CSampler Bool
bern p = CSampler $ \ name obs ->
    let dist' = Dist {logDensity = (\ x -> log (if x then p else 1 - p)),
                      sample = (\ g -> case randomR (0, 1) g of
                                         (t, g') -> (t <= p, g'))}
    in updateXRP name obs dist'

poisson :: Double -> CSampler Int
poisson l = CSampler $ \ name obs ->
    let poissonLogDensity l' x | l' > 0 && x> 0 = (fromIntegral x)*(log l') - lnFact x - l'
        poissonLogDensity l' x | x==0 = -l'
        poissonLogDensity _ _ = log 0
        dist' = Dist {logDensity = poissonLogDensity l,
                      sample = poisson_rng l}
    in updateXRP name obs dist'

gamma :: Double -> Double -> CSampler Double
gamma shape scale = CSampler $ \ name obs ->
    let dist' = Dist {logDensity = gammaLogDensity shape scale,
                      sample = gamma_rng shape scale}
    in updateXRP name obs dist'

beta :: Double -> Double -> CSampler Double
beta a b = CSampler $ \ name obs ->
    let dist' = Dist {logDensity = betaLogDensity a b,
                      sample = beta_rng a b}
    in updateXRP name obs dist'

uniform :: Double -> Double -> CSampler Double
uniform lo hi = CSampler $ \ name obs ->
    let uniformLogDensity lo' hi' x | lo' <= x && x <= hi' = log (recip (hi' - lo'))
        uniformLogDensity _ _ _ = log 0
        dist' = Dist {logDensity = uniformLogDensity lo hi,
                      sample = (\ g -> randomR (lo, hi) g)}
    in updateXRP name obs dist'

normal :: Double -> Double -> CSampler Double 
normal mu sd = CSampler $ \ name obs ->
    let dist' = Dist {logDensity = normalLogDensity mu sd,
                      sample = normal_rng mu sd}
    in updateXRP name obs dist'

laplace :: Double -> Double -> CSampler Double
laplace mu sd = CSampler $ \ name obs ->
    let dist' = Dist {logDensity = laplaceLogDensity mu sd,
                      sample = laplace_rng mu sd}
    in updateXRP name obs dist'

categorical :: (Eq a, Typeable a) => [(a,Double)] 
            -> CSampler a
categorical list = CSampler $ \ name obs ->
    let dist' = Dist {logDensity = categoricalLogDensity list,
                      sample = categoricalSample list}
    in updateXRP name obs dist'

factor :: Likelihood -> Measure ()
factor l = Measure $ \ _ -> \ s ->
   let (llTotal, llFresh) = llh2 s
   in ((), s {llh2 = (llTotal + l, llFresh)})

bind :: Measure a -> (a -> Measure b) -> Measure b
bind (Measure m) cont = Measure $ \ n ->
    sbind (m (0:n)) (\ a -> unMeasure (cont a) (1:n))

conditioned :: CSampler a -> Measure a
conditioned (CSampler f) = Measure $ \ n -> 
    \s@(S {cnds = cond:conds }) -> f n cond s{cnds = conds}

unconditioned :: CSampler a -> Measure a
unconditioned (CSampler f) = Measure $ \ n ->
    f n Nothing

instance Monad Measure where
  return = return_
  (>>=)  = bind

run :: Measure a -> [Cond] -> IO (a, Database, Likelihood)
run (Measure prog) cds = do
  g <- getStdGen
  let (v, S d ll _ _) = (prog [0]) (S M.empty (0,0) cds g)
  return (v, d, fst ll)

traceUpdate :: RandomGen g => Measure a -> Database -> [Cond] -> g
            -> (a, Database, Likelihood, Likelihood, Likelihood, g)
traceUpdate (Measure prog) d cds g = do
  -- let d1 = M.map (\ (x, l, _, ob) -> (x, l, False, ob)) d
  let d1 = M.map (\ s -> s { vis = False }) d
  let (v, S d2 (llTotal, llFresh) [] g1) = (prog [0]) (S d1 (0,0) cds g)
  let (d3, stale_d) = M.partition vis d2
  let llStale = M.foldl' (\ llStale' s -> llStale' + llhd s) 0 stale_d
  (v, d3, llTotal, llFresh, llStale, g1)

initialStep :: Measure a -> [Cond] ->
               IO (a, Database,
                   Likelihood, Likelihood, Likelihood, StdGen)
initialStep prog cds = do
  g <- getStdGen
  return $ traceUpdate prog M.empty cds g

-- TODO: Make a way of passing user-provided proposal distributions
resample :: RandomGen g => Name -> Database -> Observed -> XRP -> g ->
            (Database, Likelihood, Likelihood, Likelihood, g)
resample name db ob (XRP (x, dist)) g =
    let (x', g1) = sample dist g
        fwd = logDensity dist x'
        rvs = logDensity dist x
        l' = fwd
        newEntry = DBEntry (XRP (x', dist)) l' True ob
        db' = M.insert name newEntry db
    in (db', l', fwd, rvs, g1)

transition :: (Typeable a, RandomGen g) => Measure a -> [Cond]
           -> a -> Database -> Likelihood -> g -> [a]
transition prog cds v db ll g =
  let dbSize = M.size db
      -- choose an unconditioned choice
      (_, uncondDb) = M.partition observed db
      (choice, g1) = randomR (0, (M.size uncondDb) -1) g
      (name, (DBEntry xd _ _ ob))  = M.elemAt choice uncondDb
      (db', _, fwd, rvs, g2) = resample name db ob xd g1
      (v', db2, llTotal, llFresh, llStale, g3) = traceUpdate prog db' cds g2
      a = llTotal - ll
          + rvs - fwd
          + log (fromIntegral dbSize) - log (fromIntegral $ M.size db2)
          + llStale - llFresh
      (u, g4) = randomR (0 :: Double, 1) g3 in

  if (log u < a) then
      v' : (transition prog cds v' db2 llTotal g4)
  else
      v : (transition prog cds v db ll g4)

mcmc :: Typeable a => Measure a -> [Cond] -> IO [a]
mcmc prog cds = do
  (v, d, llTotal, _, _, g) <- initialStep prog cds
  return $ transition prog cds v d llTotal g

sample_ :: Typeable a => Measure a -> [Cond] -> IO [(a, Double)]
sample_ prog cds  = do 
  (v, d, llTotal, _, _, g) <- initialStep prog cds
  return $ map (\ x -> (x,1)) (transition prog cds v d llTotal g)

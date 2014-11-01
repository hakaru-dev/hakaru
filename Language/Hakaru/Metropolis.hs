{-# LANGUAGE RankNTypes, NoMonomorphismRestriction, BangPatterns,
  DeriveDataTypeable, GADTs, ScopedTypeVariables,
  ExistentialQuantification, StandaloneDeriving #-}
{-# OPTIONS -Wall #-}

module Language.Hakaru.Metropolis where

import qualified System.Random.MWC as MWC
import Control.Applicative
import Control.Monad
import Control.Monad.Primitive
import Data.Dynamic
import Data.Maybe

import qualified Data.Map.Strict as M
import Language.Hakaru.Types

import System.IO.Unsafe

{-

Shortcomings of this implementation

* uses parent-conditional sampling for proposal distribution
* re-evaluates entire program at every sample
* lacks way to block sample groups of variables

-}

data XRP where
  XRP :: Typeable e => (Density e, Dist e) -> XRP

unXRP :: Typeable a => XRP -> Maybe (Density a, Dist a)
unXRP (XRP (e,f)) = cast (e,f)

type Visited = Bool
type Observed = Bool
type LL = LogLikelihood

-- The first component is the LogLikelihood of the trace
-- The second is the LogLikelihood of the newly introduced
-- choices. These are used to compute the acceptance ratio
type LL2 = (LL,LL)

type Subloc = Int
type Name = [Subloc]
data DBEntry = DBEntry {
      xrp  :: XRP, 
      llhd :: LL, 
      vis  :: Visited,
      observed :: Observed }
type Database = M.Map Name DBEntry

data SamplerState where
  S :: { ldb :: Database, -- ldb = local database
         -- (total likelihood, total likelihood of XRPs newly introduced)
         llh2 :: {-# UNPACK #-} !LL2,
         cnds :: [Cond] -- conditions left to process
       } -> SamplerState

type Sampler a = PrimMonad m => SamplerState -> PRNG m -> m (a, SamplerState)

sreturn :: a -> Sampler a
sreturn x s _ = return (x, s)

sbind :: Sampler a -> (a -> Sampler b) -> Sampler b
sbind s k = \ st g -> do (v, s') <- s st g
                         k v s' g

smap :: (a -> b) -> Sampler a -> Sampler b
smap f s = sbind s (\a -> sreturn (f a))

sapp :: (Sampler (a -> b)) -> Sampler a -> Sampler b
sapp f s = \st g -> do (vf, s')  <- f st g
                       (vs, s'') <- s s' g
                       sreturn (vf vs) s'' g

newtype Measure a = Measure {unMeasure :: Name -> Sampler a }
  deriving (Typeable)

return_ :: a -> Measure a
return_ x = Measure $ \ _ -> sreturn x

updateXRP :: Typeable a => Name -> Cond -> Dist a -> Sampler a
updateXRP n obs dist' s@(S {ldb = db}) g = do
    case M.lookup n db of
      Just (DBEntry xd _ _ ob) ->
          do let Just (x, _) = unXRP xd
                 l' = logDensity dist' x
                 d1 = M.insert n (DBEntry (XRP (x,dist')) l' True ob) db
             return (fromDensity x,
                     s {ldb = d1,
                        llh2 = updateLogLikelihood (l',0) (llh2 s)})
      Nothing ->
          do (xnew2, l) <- case obs of
                             Just xdnew ->
                                 do let Just xnew = fromDynamic xdnew
                                    return $ (xnew, logDensity dist' xnew)
                             Nothing ->
                                 do xnew <- distSample dist' g
                                    return (xnew, logDensity dist' xnew)
             let d1 = M.insert n (DBEntry (XRP (xnew2, dist')) l True (isJust obs)) db
             return (fromDensity xnew2,
                     s {ldb = d1,
                        llh2 = updateLogLikelihood (l,l) (llh2 s)})

updateLogLikelihood :: LL2 -> LL2 -> LL2
updateLogLikelihood (llTotal,llFresh) (l,lf) = (llTotal+l, llFresh+lf)

factor :: LL -> Measure ()
factor l = Measure $ \ _ -> \ s _ ->
   do let (llTotal, llFresh) = llh2 s
      return ((), s {llh2 = (llTotal + l, llFresh)})

condition :: Eq b => Measure (a, b) -> b -> Measure a
condition (Measure m) b' = Measure $ \ n ->
    do let comp a b s |  a /= b = s {llh2 = (log 0, 0)}
           comp _ _ s =  s
       sbind (m n) (\ (a, b) s _ -> return (a, comp b b' s))

bind :: Measure a -> (a -> Measure b) -> Measure b
bind (Measure m) cont = Measure $ \ n ->
    sbind (m (0:n)) (\ a -> unMeasure (cont a) (1:n))

app :: Measure (a -> b) -> Measure a -> Measure b
app (Measure f) (Measure a) = Measure $ \n -> sapp (f n) (a n)

conditioned :: Typeable a => Dist a -> Measure a
conditioned dist = Measure $ \ n -> 
    \s@(S {cnds = cond:conds }) ->
        updateXRP n cond dist s{cnds = conds}

unconditioned :: Typeable a => Dist a -> Measure a
unconditioned dist = Measure $ \ n ->
    updateXRP n Nothing dist

instance Functor Measure where
  fmap f (Measure x) = Measure $ \n -> smap f (x n)

instance Applicative Measure where
  pure = return_
  (<*>) = app

instance Monad Measure where
  return = return_
  (>>=)  = bind

run :: Measure a -> [Cond] -> IO (a, Database, LL)
run (Measure prog) cds = do
  g <- MWC.create
  (v, S d ll []) <- (prog [0]) (S M.empty (0,0) cds) g
  return (v, d, fst ll)

traceUpdate :: PrimMonad m => Measure a -> Database -> [Cond] -> PRNG m
            -> m (a, Database, LL, LL, LL)
traceUpdate (Measure prog) d cds g = do
  -- let d1 = M.map (\ (x, l, _, ob) -> (x, l, False, ob)) d
  let d1 = M.map (\ s -> s { vis = False }) d
  (v, S d2 (llTotal, llFresh) []) <- (prog [0]) (S d1 (0,0) cds) g
  let (d3, stale_d) = M.partition vis d2
  let llStale = M.foldl' (\ llStale' s -> llStale' + llhd s) 0 stale_d
  return (v, d3, llTotal, llFresh, llStale)

initialStep :: Measure a -> [Cond] ->
               PRNG IO -> IO (a, Database, LL, LL, LL)
initialStep prog cds g = traceUpdate prog M.empty cds g

-- TODO: Make a way of passing user-provided proposal distributions
resample :: PrimMonad m => Name -> Database -> Observed -> XRP -> PRNG m ->
            m (Database, LL, LL, LL)
resample name db ob (XRP (x, dist)) g =
    do x' <- distSample dist g
       let fwd = logDensity dist x'
           rvs = logDensity dist x
           l' = fwd
           newEntry = DBEntry (XRP (x', dist)) l' True ob
           db' = M.insert name newEntry db
       return (db', l', fwd, rvs)

transition :: (Typeable a) => Measure a -> [Cond]
           -> a -> Database -> LL -> PRNG IO -> IO [a]
transition prog cds v db ll g =
  do let dbSize = M.size db
         -- choose an unconditioned choice
         (_, uncondDb) = M.partition observed db
     choice <- MWC.uniformR (0, (M.size uncondDb) -1) g
     let (name, (DBEntry xd _ _ ob))  = M.elemAt choice uncondDb
     (db', _, fwd, rvs) <- resample name db ob xd g
     (v', db2, llTotal, llFresh, llStale) <- traceUpdate prog db' cds g
     let a = llTotal - ll
             + rvs - fwd
             + log (fromIntegral dbSize) - log (fromIntegral $ M.size db2)
             + llStale - llFresh
     u <- MWC.uniformR (0 :: Double, 1) g
     if (log u < a) then
         liftM ((:) v') $ unsafeInterleaveIO (transition prog cds v' db2 llTotal g)
     else
         liftM ((:) v) $ unsafeInterleaveIO (transition prog cds v db ll g)

mcmc :: Typeable a => Measure a -> [Cond] -> IO [a]
mcmc prog cds = do
  g <- MWC.create
  (v, d, llTotal, _, _) <- initialStep prog cds g
  transition prog cds v d llTotal g

sample :: Typeable a => Measure a -> [Cond] -> IO [(a, Double)]
sample prog cds  = do 
  g <- MWC.create
  (v, d, llTotal, _, _) <- initialStep prog cds g
  (transition prog cds v d llTotal g) >>= return . map (\ x -> (x,1)) 

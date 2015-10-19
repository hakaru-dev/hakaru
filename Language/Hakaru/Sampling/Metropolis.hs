{-# LANGUAGE RankNTypes
           , NoMonomorphismRestriction
           , BangPatterns
           , DeriveDataTypeable
           , GADTs
           , ScopedTypeVariables
           , ExistentialQuantification
           , StandaloneDeriving
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2015.10.18
-- |
-- Module      :  Language.Hakaru.Sampling.Metropolis
-- Copyright   :  Copyright (c) 2015 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- Shortcomings of this implementation:
--
-- * uses parent-conditional sampling for proposal distribution
-- * re-evaluates entire program at every sample
-- * lacks way to block sample groups of variables
----------------------------------------------------------------
module Language.Hakaru.Sampling.Metropolis where

import Control.Applicative
import Control.Monad.Primitive
import Data.Dynamic
import System.IO.Unsafe
import qualified System.Random.MWC as MWC
import qualified Data.Map.Strict   as M

import Language.Hakaru.Sampling.Types
----------------------------------------------------------------

data XRP where
    XRP :: Typeable e => Density e -> Dist e -> XRP

unXRP :: Typeable a => XRP -> Maybe (Density a, Dist a)
unXRP (XRP e f) = cast (e,f)

type Visited  = Bool
type Observed = Bool
type LL       = LogLikelihood
type Subloc   = Int
type Name     = [Subloc]

-- TODO: can't any\/all of these fields be made strict?
data DBEntry = DBEntry
    { xrp      :: XRP
    , llhd     :: LL -- TODO: better name. What the heck does this *mean*?
    , visited  :: Visited
    , observed :: Observed
    }
    
type Database = M.Map Name DBEntry

-- TODO: can't any\/all of these fields be made strict?
-- TODO: clean up all the places where we actually pattern match on SamplerState
-- | 'totalLL' and 'freshLL' are used together to compute the acceptance ratio.
data SamplerState = SamplerState
    { localDB    :: Database -- ^ local database
    , totalLL    :: LL       -- ^ total likelihood of the trace
    , freshLL    :: LL       -- ^ likelihood of newly introduced choices
    , conditions :: [Cond]   -- ^ conditions left to process
    }

-- TODO: make this a newtype and give it functor\/applicative\/monad instances, in order to avoid the namespace pollution below.
type Sampler a = (Functor m, PrimMonad m) => SamplerState -> PRNG m -> m (a, SamplerState)

sreturn :: a -> Sampler a
sreturn x s _ = return (x, s)

sbind :: Sampler a -> (a -> Sampler b) -> Sampler b
sbind mx k = \s g -> do
    (x, s') <- mx s g
    k x s' g

smap :: (a -> b) -> Sampler a -> Sampler b
smap f mx = mx `sbind` \x -> sreturn (f x)
    -- == \s g -> first f <$> mx s g

sapp :: Sampler (a -> b) -> Sampler a -> Sampler b
sapp mf mx = \s g -> do
    (f, s')  <- mf s  g
    (x, s'') <- mx s' g
    sreturn (f x) s'' g

newtype Measure a = Measure { unMeasure :: Name -> Sampler a }
    deriving (Typeable)

-- TODO: what value is there in having the name be the first argument? We could get rid of the 'Sampler' type alias if only we reordered the name to be the last argument. Notably, this also eliminates some eta expansion in the use sites (since the name is just passed through from outside)
updateXRP :: Typeable a => Name -> Cond -> Dist a -> Sampler a
updateXRP n obs dist s@(SamplerState {localDB = db}) g = do
    -- As a performance hack, we use @isFresh*l@ instead of @if isFresh then l else 0@
    (x, ob, isFresh) <-
        case M.lookup n db of
        Just (DBEntry xd _ _ ob) ->
            case unXRP xd of
            Just (x, _) -> return (x, ob, 0)
            Nothing     -> error "updateXRP: unXRP failed"
        Nothing ->
            case obs of
            Just xd ->
                case fromDynamic xd of
                Just x  -> return (x, True, 1)
                Nothing -> error "updateXRP: fromDynamic failed"
            Nothing -> do
                x <- distSample dist g
                return (x, False, 1)
    --
    let l   = logDensity dist x
        db' = M.insert n (DBEntry (XRP x dist) l True ob) db
    return
        ( fromDensity x
        , s { localDB = db'
            , totalLL = totalLL s + l
            , freshLL = freshLL s + isFresh*l
            }
        )

factor :: LL -> Measure ()
factor l = Measure $ \_ s _ -> return ((), s {totalLL = l + totalLL s})
    -- TODO: make the 'totalLL' update strict?

condition :: Eq b => Measure (a, b) -> b -> Measure a
condition (Measure m) b' = Measure $ \n ->
    m n `sbind` \ (a, b) s _ ->
    return (a, comp b b' s)
    where
    comp a b s
        | a /= b    = s {totalLL = log 0, freshLL = 0}
        | otherwise = s


conditioned :: Typeable a => Dist a -> Measure a
conditioned dist =
    Measure $ \n s@(SamplerState {conditions = c:cs}) ->
        updateXRP n c dist s{conditions = cs}

unconditioned :: Typeable a => Dist a -> Measure a
unconditioned dist = Measure $ \n ->
    updateXRP n Nothing dist

instance Functor Measure where
    fmap f (Measure x) = Measure $ \n -> smap f (x n)

instance Applicative Measure where
    pure x                  = Measure $ \_ -> sreturn x
    Measure f <*> Measure a = Measure $ \n -> sapp (f n) (a n)

instance Monad Measure where
    return          = pure
    Measure m >>= k = Measure $ \n ->
        m (0:n) `sbind` \a ->
        unMeasure (k a) (1:n)

run :: Measure a -> [Cond] -> IO (a, Database, LL)
run (Measure prog) cds = do
    g <- MWC.create
    (v, SamplerState db llTotal _ []) <- prog [0] (SamplerState M.empty 0 0 cds) g
    return (v, db, llTotal)

traceUpdate
    :: (Functor m, PrimMonad m)
    => Measure a -> Database -> [Cond] -> PRNG m
    -> m (a, Database, LL, LL, LL)
traceUpdate (Measure prog) db0 cds g = do
    -- let db1 = M.map (\ (x, l, _, ob) -> (x, l, False, ob)) db0
    let db1 = M.map (\s -> s { visited = False }) db0
    (v, SamplerState db2 llTotal llFresh []) <- prog [0] (SamplerState db1 0 0 cds) g
    let (db3, staleDB) = M.partition visited db2
    let llStale = M.foldl' (\acc s -> acc + llhd s) 0 staleDB
    return (v, db3, llTotal, llFresh, llStale)

initialStep
    :: Measure a -> [Cond] -> PRNG IO -> IO (a, Database, LL, LL, LL)
initialStep prog cds g = traceUpdate prog M.empty cds g

-- TODO: Make a way of passing user-provided proposal distributions
resample
    :: (Functor m, PrimMonad m)
    => Name -> Database -> Observed -> XRP -> PRNG m
    -> m (Database, LL, LL, LL)
resample name db ob (XRP x dist) g = do
    x' <- distSample dist g
    let fwd = logDensity dist x'
        rvs = logDensity dist x
        l' = fwd
        newEntry = DBEntry (XRP x' dist) l' True ob
        db' = M.insert name newEntry db
    return (db', l', fwd, rvs)

transition
    :: (Typeable a)
    => Measure a -> [Cond] -> a -> Database -> LL -> PRNG IO -> IO [a]
transition prog cds v db ll g = do
    let dbSize = M.size db
        -- choose an unconditioned choice
        (_, uncondDb) = M.partition observed db
    choice <- MWC.uniformR (0, (M.size uncondDb) -1) g
    let (name, DBEntry xd _ _ ob) = M.elemAt choice uncondDb
    (db', _, fwd, rvs) <- resample name db ob xd g
    (v', db2, llTotal, llFresh, llStale) <- traceUpdate prog db' cds g
    let a = llTotal - ll
            + rvs - fwd
            + log (fromIntegral dbSize) - log (fromIntegral $ M.size db2)
            + llStale - llFresh
    u <- MWC.uniformR (0 :: Double, 1) g
    if log u < a
        then (v' :) <$> unsafeInterleaveIO (transition prog cds v' db2 llTotal g)
        else (v :) <$> unsafeInterleaveIO (transition prog cds v db ll g)

mcmc :: Typeable a => Measure a -> [Cond] -> IO [a]
mcmc prog cds = do
    g <- MWC.create
    (v, d, llTotal, _, _) <- initialStep prog cds g
    transition prog cds v d llTotal g

sample :: Typeable a => Measure a -> [Cond] -> IO [(a, Double)]
sample prog cds  = do 
    g <- MWC.create
    (v, d, llTotal, _, _) <- initialStep prog cds g
    map (\x -> (x,1)) <$> transition prog cds v d llTotal g

----------------------------------------------------------------
----------------------------------------------------------- fin.
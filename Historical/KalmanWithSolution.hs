{-# OPTIONS -W #-}
module Historical.KalmanWithSolution where

import qualified Numeric.Integration.TanhSinh as TanhSinh
import Control.Parallel (par)
-- for parallelism, say "ghci +RTS -N -RTS KalmanWithSolution.hs"

-- type for densities/distributions
type D a = (a -> Double) -> Double

-- density which corresponds to Lebesgue, i.e. uniform on R.
lebesgue :: D Double
lebesgue = \k -> TanhSinh.result
                   (last
                     (TanhSinh.everywhere TanhSinh.parTrap k))
           -- not in tail form! depends on a specific answer type!

{-  In direct style:
    lebesgue () = shift k.
                    TanhSinh.result
                      (TanhSinh.absolute 1e-6
                        (TanhSinh.everywhere TanhSinh.parTrap k))
 -}

square :: Double -> Double
square x = x * x

data Normal = Normal { mean, std :: Double } deriving (Show)

density :: Normal -> Double -> Double
density d x = exp (square ((x - mean d) / std d) / (-2))
            / sqrt (2 * pi) / std d

reflect :: Normal -> D Double
reflect d = \k -> lebesgue (\x -> density d x * k x)
            -- not in tail form! depends on a specific answer type!

{-  In direct style:
    reflect d = let x = lebesgue ()
                in shift k. density d x * k x
 -}

-- Takes a density, assumes that it is normal, and reifies it by using its
-- first 3 moments. Actually terminates for all proper densities, but will
-- return a 'normal truncation' of its moment generating function

reify :: D Double -> Normal
reify d = let t0   = d (\_ -> 1)
              t1   = d id
              t2   = d square
              mean = t1 / t0
          in t0 `par` t1 `par` t2 `par`
             Normal mean (sqrt (t2 / t0 - square mean))

{-  In direct style:
    reify d = let t0   = reset (fun () -> let _ = d () in 1)
                  t1   = reset m
                  t2   = reset (fun () -> square (d ()))
                  mean = t1 / t0
              in t0 `par` t1 `par` t2 `par`
                 Normal mean (sqrt (t2 / t0 - square mean))
 -}

observe :: Normal -> Double -> D ()
observe d o = \k -> density d o * k ()
              -- not in tail form! depends on a specific answer type!

{-  In direct style:
    observe d o = shift k. density d o * k ()
 -}

-- Example: Put something           at 10 +/- 3
--          Look and see that it is at  9 +/- 1
--          Combine prior knowledge and observation
-- Try "reify ex1"
ex1 :: D Double
ex1 = \k -> reflect (Normal 10 3) (\x ->
            observe (Normal x 1) 9 (\() ->
            k x))

{-  In direct style:
    ex1 () = let x  = reflect (Normal 10 3)
                 () = observe (Normal x 1) 9
             in x
 -}

-- Example: Put something           at 10 +/- 3
--          Look and see that it is at  9 +/- 1
--          Push and move it        by  5 +/- 2
--          Look again and see it   at 13 +/- 1
--          Combine prior knowledge and observation
-- Try "reify ex2"
ex2 :: D Double
ex2 = \k -> reflect (Normal 10 3) (\x ->
            observe (Normal x 1) 9 (\() ->
            reflect (Normal (x+5) 2) (\x' ->
            observe (Normal x' 1) 13 (\() ->
            k x'))))
-- Exercise: What if the successive observed positions are not 9 and 13?
-- Change the calls above to "observe" and try "reify ex2" some more.
-- What changes in the output and what doesn't?

{-  In direct style:
    ex2 () = let x  = reflect (Normal 10 3)
                 () = observe (Normal x 1) 9
                 x' = reflect (Normal (x+5) 2)
                 () = observe (Normal x' 1) 13
             in x'
 -}

-- Example: Put something           at 10 +/- 3
--          Look and see that it is at  9 +/- 1
--          Push and move it        by  5 +/- 2
--          Look again and see it   at 13 +/- 1
--          Push and move it        by  5 +/- 2
--          Combine prior knowledge and observation
-- Try "reify ex3" (but don't let it overheat your computer)
ex3 :: D Double
ex3 = \k -> reflect (Normal 10 3) (\x ->
            observe (Normal x 1) 9 (\() ->
            reflect (Normal (x+5) 2) (\x' ->
            observe (Normal x' 1) 13 (\() ->
            reflect (Normal (x'+5) 2) k))))
-- Memoize nested integral to speed up computation
-- Try "reify ex3memoized"
ex3aux :: Normal
ex3aux = reify (\k -> reflect (Normal 10 3) (\x ->
                      observe (Normal x 1) 9 (\() ->
                      reflect (Normal (x+5) 2) k)))
ex3memoized :: D Double
ex3memoized = \k -> reflect ex3aux (\x' ->
                    observe (Normal x' 1) 13 (\() ->
                    reflect (Normal (x'+5) 2) k))

{-  In direct style:
    ex3 () = let x  = reflect (Normal 10 3)
                 () = observe (Normal x 1) 9
                 x' = reflect (Normal (x+5) 2)
                 () = observe (Normal x' 1) 13
             in reflect (Normal (x'+5) 2)
 -}

-- Exercise: A Kalman filter. Write a function "drift"
drift :: Double -> Double -> D Double
-- so that "drift x o" means: Start                   at x
--                            Push and move it        by 5 +/- 2
--                            Look and see that it is at o +/- 1
drift x o = \k -> reflect (Normal (x+5) 2) (\x' ->
                  observe (Normal x' 1) o (\() ->
                  k x'))
-- Try "drifts (Normal 10 3) [14,19,24]"
drifts :: Normal -> [Double] -> [Normal]
drifts d []     = [d]
drifts d (o:os) = d : drifts (reify (\k -> reflect d (\x -> drift x o k))) os

{-# OPTIONS -W #-}

module LazyMcmc where

import System.Random (RandomGen, randomR, getStdRandom)
import Control.Monad (when, replicateM_)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.RWS (RWST, execRWST, asks, tell, gets, modify)
import Control.Monad.Trans.State (State, runState, state)
import Data.Maybe (fromMaybe, isNothing)
import Data.Monoid
import qualified Data.Map as M
import Text.PrettyPrint
import Util.Pretty

type Prob = Double

choose :: (RandomGen g) => [(k, Prob)] -> g -> ((k, Prob), g)
choose kps g0 =
  let total = sum (map snd kps)
      (p, g) = randomR (0, total) g0
      f (k,v) b p0 = let p1 = p0 + v in if p <= p1 then k else b p1
      err p0 = error ("choose: failure p0=" ++ show p0 ++
                      " total=" ++ show total ++
                      " length=" ++ show (length kps))
  in ((foldr f err kps 0, total), g)

type Subloc = Int
type Loc = [Subloc]

root :: Loc
root = []

data Value = Bool Bool deriving (Eq, Show) -- | Fun (Loc -> Code)
instance Pretty Value

data Condition = Known Value | Proposed [Value] deriving (Eq, Show)
instance Pretty Condition

known :: Condition -> Maybe Value
known (Known v   ) = Just v
known (Proposed _) = Nothing

-- This is our language.
data Code = CEvaluate [Loc] ([Value] -> Code)
          | CAllocate Code  (Loc     -> Code)
          | CGenerate [(Value, Prob)]
  deriving (Show)

bernoulli :: Prob -> Code
bernoulli p = CGenerate [(Bool True, p), (Bool False, 1-p)]

arora_example :: Code
arora_example = CAllocate (bernoulli 0.5) $ \w ->
                CEvaluate [w] $ \[Bool w] ->
                if w then CAllocate (bernoulli 0.5) $ \r ->
                          CEvaluate [r] $ \[Bool r] ->
                          if r then bernoulli 0.4 else bernoulli 0.8
                     else bernoulli 0.2

xor_sequence :: Code
xor_sequence = CAllocate (bernoulli 0.5) $ \stop ->
               CEvaluate [stop] $ \[Bool stop] ->
               if stop then bernoulli 0.9
                       else CAllocate xor_sequence $ \rest ->
                            CEvaluate [rest] $ \[Bool rest] ->
                            bernoulli (if rest then 0.1 else 0.9)

data Trace = TEvaluate [Loc] ([Value] -> Code) (Maybe Trace)
           | TAllocate Code  (Loc     -> Code) (Maybe Trace)
           | TGenerate [(Value, Prob)]         (Maybe ())
  deriving (Show)

instance Pretty Trace where
  pretty (TEvaluate locs _ trace) =
    pretty' trace (text "TEvaluate" <+> text (show locs) <+> text "_")
  pretty (TAllocate _    _ trace) =
    pretty' trace (text "TAllocate" <+> text "_" <+> text "_")
  pretty (TGenerate dist   trace) =
    text "TGenerate" <+> text (show dist) <+> text (show trace)

pretty' :: Maybe Trace -> Doc -> Doc
pretty' Nothing      doc = doc <+> text "$" <+> text "Nothing"
pretty' (Just trace) doc = doc <+> text "$" <+> text "Just" <+> text "$"
                           $+$ pretty trace

code :: Trace -> Code
code (TEvaluate locs k _) = CEvaluate locs k
code (TAllocate code k _) = CAllocate code k
code (TGenerate dist   _) = CGenerate dist

fresh :: Code -> Trace
fresh (CEvaluate locs k) = TEvaluate locs k Nothing
fresh (CAllocate code k) = TAllocate code k Nothing
fresh (CGenerate dist  ) = TGenerate dist   Nothing

type Heap = M.Map Loc (Trace, Maybe Condition)
type M g = RWST Heap (Product Prob) Heap (State g)

evalLoc :: (RandomGen g) => Loc -> M g ()
evalLoc loc = do
  let process trace target@(Just (Proposed _)) =
        modify (M.insert loc (trace, target))
      process trace (Just (Known v)) = do
        (trace, target) <- eval loc 0 trace (Just v)
        modify (M.insert loc (trace, fmap Known target))
      process trace Nothing = do
        (trace, target) <- eval loc 0 trace Nothing
        modify (M.insert loc (trace, fmap Known target))
  next <- gets (M.lookup loc)
  prev <- asks (M.lookup loc)
  case (next, prev) of
    (Just (_    , Just _ ), _                   ) -> return ()
    (Just (_    , Nothing), Just (trace, target)) -> process trace target
    (Just (trace, Nothing), Nothing             ) -> process trace Nothing
    (Nothing              , Just (trace, target)) -> process trace target
    (Nothing              , Nothing             ) ->
      error ("unknown location " ++ show loc)

eval :: (RandomGen g) => Loc -> Subloc ->
        Trace -> Maybe Value -> M g (Trace, Maybe Value)
eval loc subloc (TEvaluate locs k trace) target = do
  let f loc = do evalLoc loc
                 Just (_, Just cond) <- gets (M.lookup loc)
                 return cond
  conds <- mapM f locs
  case mapM known conds of
    Nothing -> return (TEvaluate locs k Nothing, target)
    Just vs -> do
      (trace, target) <- eval loc subloc
                           (fromMaybe (fresh (k vs)) trace) target
      return (TEvaluate locs k (Just trace), target)
eval loc subloc (TAllocate code k trace) target = do
  let newloc = subloc:loc
  modify (M.insert newloc (fresh code, Nothing))
  (trace, target) <- eval loc (succ subloc)
                       (fromMaybe (fresh (k newloc)) trace) target
  return (TAllocate code k (Just trace), target)
eval _loc _subloc (TGenerate dist trace) target = do
  let dist' = case target of Nothing -> dist
                             Just v  -> filter ((v ==) . fst) dist
  (v, p) <- lift (state (choose dist'))
  when (isNothing trace) (tell (Product p))
  return (TGenerate dist (Just ()), Just v)

initial :: Code -> Maybe Value -> Heap
initial code v = M.singleton root (fresh code, fmap Known v)

run :: Heap -> IO (Heap, Prob)
run heap = do
  (h,p) <- getStdRandom $ runState
                        $ (fmap.fmap) getProduct
                        $ execRWST (evalLoc root) heap M.empty
  print (pretty h)
  print p
  putStrLn ""
  return (h,p)

propose :: Loc -> Heap -> Heap
propose = M.adjust f where
  f (trace, Just (Known v)) =
    (fresh (code trace),
     Just (Proposed (filter (v /=) [Bool True, Bool False])))

original :: Heap -> Heap -> Heap
original = M.unionWith f where
  f _           core@(_, Just (Known _))   = core
  f (_, target) (trace, Just (Proposed _)) = (trace, target)
  f prev        _                          = prev

proposals :: Loc -> Heap -> [Heap]
proposals loc core =
  let Just (_, Just (Proposed vs)) = M.lookup loc core
  in [ M.adjust (\(trace, _) -> (trace, Just (Known v))) loc core | v <- vs ]

main :: IO ()
main = replicateM_ 10 $ do
    putStrLn "=== Initial sample ==="
    (prev,_) <- run (initial xor_sequence{-arora_example-} (Just (Bool True)))
    putStrLn "=== Proposal core ==="
    (core,_) <- run (propose [0] prev)
    putStrLn "=== Rejection considered ==="
    run (original prev core)
    putStrLn "=== Acceptance considered ==="
    mapM_ run (proposals [0] core)

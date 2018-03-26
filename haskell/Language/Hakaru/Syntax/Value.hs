{-# LANGUAGE CPP
           , DataKinds
           , PolyKinds
           , GADTs
           , TypeOperators
           , EmptyCase
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
module Language.Hakaru.Syntax.Value where

import           Language.Hakaru.Syntax.IClasses
import           Language.Hakaru.Syntax.Datum
import           Language.Hakaru.Types.HClasses
import           Language.Hakaru.Types.DataKind
import           Language.Hakaru.Types.Coercion
import           Language.Hakaru.Types.Sing

import           Data.STRef

import qualified Data.Vector                     as V
import qualified Data.Number.LogFloat            as LF
import           Data.Number.Natural

import qualified System.Random.MWC               as MWC

data Value :: Hakaru -> * where
     VNat     ::                !Natural -> Value 'HNat
     VInt     ::                !Integer -> Value 'HInt
     VProb    :: {-# UNPACK #-} !LF.LogFloat -> Value 'HProb
     VReal    :: {-# UNPACK #-} !Double -> Value 'HReal

     VDatum   :: !(Datum Value (HData' t)) -> Value (HData' t)

     -- Assuming you want to consider lambdas/closures to be values.
     -- N.B., the type below is larger than is correct; that is,
     VLam     :: (Value a -> Value b) -> Value (a ':-> b)

     -- Measures hold their importance weight and random seed
     VMeasure :: (Value 'HProb ->
                  MWC.GenIO    ->
                  IO (Maybe (Value a, Value 'HProb))
                 ) -> Value ('HMeasure a)
     VArray   :: {-# UNPACK #-} !(V.Vector (Value a)) -> Value ('HArray a)

instance Eq1 Value where
    eq1 (VNat  a) (VNat  b)   = a == b
    eq1 (VInt  a) (VInt  b)   = a == b
    eq1 (VProb a) (VProb b)   = a == b
    eq1 (VReal a) (VReal b)   = a == b
    eq1 (VDatum a) (VDatum b) = a == b
    eq1 (VArray a) (VArray b) = a == b
    eq1 _        _            = False

instance Eq (Value a) where
    (==) = eq1

instance Show1 Value where
    showsPrec1 p (VNat   v)   = showsPrec  p v
    showsPrec1 p (VInt   v)   = showsPrec  p v
    showsPrec1 p (VProb  v)   = showsPrec  p v
    showsPrec1 p (VReal  v)   = showsPrec  p v
    showsPrec1 p (VDatum d)   = showsPrec1 p d
    showsPrec1 _ (VLam   _)   = showString "<function>"
    showsPrec1 _ (VMeasure _) = showString "<measure>"
    showsPrec1 p (VArray e)   = showsPrec  p e

instance Show (Value a) where
    showsPrec = showsPrec1
    show      = show1

instance Coerce Value where
    coerceTo   CNil         v = v
    coerceTo   (CCons c cs) v = coerceTo cs (primCoerceTo c v)

    coerceFrom CNil         v = v
    coerceFrom (CCons c cs) v = primCoerceFrom c (coerceFrom cs v)

instance PrimCoerce Value where
    primCoerceTo c l =
        case (c,l) of
        (Signed HRing_Int,            VNat  a) -> VInt  $ fromNatural a
        (Signed HRing_Real,           VProb a) -> VReal $ LF.fromLogFloat a
        (Continuous HContinuous_Prob, VNat  a) ->
            VProb $ LF.logFloat (fromIntegral (fromNatural a) :: Double)
        (Continuous HContinuous_Real, VInt  a) -> VReal $ fromIntegral a

    primCoerceFrom c l =
        case (c,l) of
        (Signed HRing_Int,            VInt  a) -> VNat  $ unsafeNatural a
        (Signed HRing_Real,           VReal a) -> VProb $ LF.logFloat a
        (Continuous HContinuous_Prob, VProb a) ->
            VNat $ unsafeNatural $ floor (LF.fromLogFloat a :: Double)
        (Continuous HContinuous_Real, VReal a) -> VInt  $ floor a


lam2 :: Value (a ':-> b ':-> c) -> (Value a -> Value b -> Value c)
lam2 (VLam f1) v1 =
    case f1 v1 of
    VLam f2 -> f2

enumFromUntilValue
    :: (HDiscrete a)
    -> Value a
    -> Value a
    -> [Value a]
enumFromUntilValue _ (VNat lo) (VNat hi) = map VNat (init (enumFromTo lo hi))
enumFromUntilValue _ (VInt lo) (VInt hi) = map VInt (init (enumFromTo lo hi))

data VReducer :: * -> Hakaru -> * where
     VRed_Num    :: STRef s (Value a)
                 -> VReducer s a
     VRed_Unit   :: VReducer s HUnit
     VRed_Pair   :: Sing a
                 -> Sing b
                 -> VReducer s a
                 -> VReducer s b
                 -> VReducer s (HPair a b)
     VRed_Array  :: V.Vector (VReducer s a)
                 -> VReducer s ('HArray a)

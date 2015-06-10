{-# LANGUAGE 
    TemplateHaskell
  , DeriveDataTypeable
  , QuasiQuotes
  , DataKinds
  , TypeFamilies
  , RankNTypes
  , ScopedTypeVariables
  , DataKinds
  #-}
{-# OPTIONS -fno-warn-missing-signatures -W #-}

-- This option causes the compilation of this module to dump the derived
-- code. For some reason, hint believes that this is a compiler error and quits.
-- {-# OPTIONS -ddump-splices #-}

module Tests.EmbedDatatypes where 

import Language.Hakaru.Embed
import Language.Hakaru.Syntax 
import Language.Hakaru.Simplify

import Language.Hakaru.Maple 

embeddable [d| data BoolProb = BoolProb HBool HProb |] 

embeddable [d| data Real5 = Real5 { r1, r2, r3, r4, r5 :: HReal} |]

embeddable [d| data P2 a b = P2 { p2_fst :: a, p2_snd :: b } |]

embeddableWith (defaultConfig { mkCaseFun = const "if'" })
  [d| data Boolean = True_ | False_ |]
  
embeddable [d| data P3 a b c = P3 {xx :: P2 a b, yy :: c} |]

embeddable [d| data List a = Nil | Cons a (List a) |] 

consL :: Embed r => r a -> r (List a) -> r (List a)
consL x xs = sop (S $ Z $ RK x :* RI xs :* Nil)

test0 :: Maple (List HInt)
test0 = consL 1 $ consL 2 $ consL 3 (mkList (Z Nil))

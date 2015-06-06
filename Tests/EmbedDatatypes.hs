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

-- BUG: this one no longer works with our Hakaru* datakind, because Hakaru types don't have SingI instances...
-- embeddable [d| data BoolProb = BoolProb HBool HProb |] 

-- BUG: this one no longer works with our Hakaru* datakind, because Hakaru types don't have SingI instances...
-- embeddable [d| data Real5 = Real5 { r1, r2, r3, r4, r5 :: HReal} |]

-- BUG: this one no longer kind-checks with our Hakaru* datakind
-- embeddable [d| data P2 a b = P2 { p2_fst :: a, p2_snd :: b } |]

embeddableWith (defaultConfig { mkCaseFun = const "if'" })
  [d| data Boolean = True_ | False_ |]
  
-- BUG: No longer works, since P2 no longer works
-- embeddable [d| data P3 a b c = P3 {xx :: P2 a b, yy :: c} |]

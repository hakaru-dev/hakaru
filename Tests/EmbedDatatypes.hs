{-# LANGUAGE 
    TemplateHaskell
  , DeriveDataTypeable
  , QuasiQuotes
  , DataKinds
  , TypeFamilies
  , RankNTypes
  , ScopedTypeVariables
  #-}
{-# OPTIONS -ddump-splices -fno-warn-missing-signatures -W #-}

module Tests.EmbedDatatypes where 

import Language.Hakaru.Embed
import Language.Hakaru.Syntax 
import Language.Hakaru.Simplify
import Prelude hiding (Real) 

embeddable [d| data BoolProb = BoolProb Bool Prob |] 

embeddable [d| data Real5 = Real5 { r1, r2, r3, r4, r5 :: Real} |]

embeddable [d| data P2 a b = P2 { p2_fst :: a, p2_snd :: b } |]

embeddableWith (defaultConfig { mkCaseFun = const "if'" })
  [d| data Boolean = True_ | False_ |]


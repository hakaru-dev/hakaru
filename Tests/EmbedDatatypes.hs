{-# LANGUAGE TemplateHaskell, DeriveDataTypeable, QuasiQuotes, DataKinds, TypeFamilies #-}

module Tests.EmbedDatatypes where 

import Language.Hakaru.Embed
import Language.Hakaru.Syntax 
import Prelude hiding (Real) 

embeddable [d| data BoolProb = BoolProb Bool Prob |] 

embeddable [d| data Real5 = Real5 { r1, r2, r3, r4, r5 :: Real} |]

embeddable [d| data P2 a b = P2 { p2_fst :: a, p2_snd :: b } |]

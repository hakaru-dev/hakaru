{-# LANGUAGE DataKinds,
             FlexibleContexts,
             GADTs #-}

module HKC.Flatten where

import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.ABT

import Language.C.Data.Node
import Language.C.Data.Position
import Language.C.Syntax.AST

flatten :: ABT Term abt => abt xs a -> CTranslUnit
flatten e =
  let n = undefNode in
  case viewABT e of
    _           -> CTranslUnit [CDeclExt (CDecl [CTypeSpec (CIntType n)] [] n)] n
    -- (Syn t)    -> CTranslUnit [] undefNode
    -- (Var x)    -> CTranslUnit [] undefNode
    -- (Bind x v) -> CTranslUnit [] undefNode

-- header :: Text

-- build :: Text -> Text
-- build p = mconcat
--   [[r|#include <time.h>
-- #include <stdlib.h>
-- #include <stdio.h>
-- #include <math.h>
-- |]
--    ,normalC
--    ,[r|void main(){ srand(time(NULL)); while(1) { printf("%.17g\n",|]
--    ,p
--    ,[r|);}
-- }|]
--   ]

-- normalC :: Text
-- normalC =
--   [r|double normal(double mu, double sd) {
--   double u = ((double)rand() / (RAND_MAX)) * 2 - 1;
--   double v = ((double)rand() / (RAND_MAX)) * 2 - 1;
--   double r = u*u + v*v;
--   if (r==0 || r>1) return normal(mu,sd);
--   double c = sqrt(-2 * log(r) / r);
--   return mu + u * c * sd;
--   }
-- |]

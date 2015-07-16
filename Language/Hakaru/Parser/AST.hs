{-# LANGUAGE RankNTypes, GADTs, ExistentialQuantification, StandaloneDeriving #-}
module Language.Hakaru.Parser.AST where

import Language.Hakaru.Syntax.DataKind
import Language.Hakaru.Syntax.AST()

type Name = String

-- Base/Integrate/Lambda/Order/Num/Floating/Fractional repr
-- Does not include pi_, exp_, erf_, log_, sqrt_ or
--                  vector, index, size
data UExpr =
    Unit |
    Var Name |
    Pair UExpr UExpr |
    Unpair UExpr UExpr |

    Double Double |
    Int Int |
    Bool Bool |

    Times UExpr UExpr |
    Divide UExpr UExpr |
    Plus UExpr UExpr |
    Minus UExpr UExpr |

    Lt_ UExpr UExpr |
    Eq_ UExpr UExpr |

    InL UExpr |
    InR UExpr |
    Uneither UExpr UExpr UExpr |

    If UExpr UExpr UExpr |

    Nil |
    Cons UExpr UExpr |

    UnsafeProb UExpr |
    FromProb UExpr |
    FromInt UExpr |
                    
    Pi |
    Exp UExpr  |
    Erf UExpr  |
    Log UExpr  |
    Sqrt UExpr |
    Pow UExpr UExpr |

    Infinity | NegInfinity |

    GammaFunc UExpr |
    BetaFunc UExpr UExpr |

    Fix UExpr |
    Lam UExpr UExpr |
    Let UExpr UExpr UExpr |
    App UExpr UExpr |

    Integrate UExpr UExpr UExpr |
    Summate UExpr UExpr UExpr |
  
    Dist Dist
 deriving (Eq, Show)


-- Mochastic repr, not including mix, dp, chain and plate
data Dist =
    Dirac UExpr |
    Bind UExpr Dist Dist |
    Lebesgue |
    Counting |
    Superpose UExpr |
    Uniform UExpr UExpr |
    Normal UExpr UExpr |
    Categorical UExpr |
    Poisson UExpr |
    Gamma UExpr UExpr |
    Beta UExpr UExpr
 deriving (Eq, Show)

data Value' =
   | Nat
   | Int
   | Prob
   | Real
   | Datum

data AST' a =
   | Var Name
   | Op a
   | Lam Name (AST' a) 
   | App (AST' a) (AST' a)
   | Let Name (AST' a) (AST' a)
   | Ann (AST' a) Hakaru
   | Value Value'
   | Empty
   | Array (AST' a) Name (AST' a)
   | Case  AST' [Branch']
   | Bind  Name (AST' a) (AST' a)
   | Superpose [((AST' a), (AST' a))]

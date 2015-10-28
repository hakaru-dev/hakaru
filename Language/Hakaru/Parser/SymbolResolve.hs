{-# LANGUAGE RankNTypes,
             GADTs,
             OverloadedStrings,
             ExistentialQuantification,
             StandaloneDeriving #-}
module Language.Hakaru.Parser.SymbolResolve where

import Data.List
import Data.Text hiding (maximum)

import Language.Hakaru.Syntax.DataKind hiding (Symbol)
import qualified Language.Hakaru.Syntax.AST as T
import qualified Language.Hakaru.Parser.AST as U
import Language.Hakaru.Syntax.Sing
import Language.Hakaru.Syntax.IClasses
import Language.Hakaru.Syntax.HClasses
import qualified Language.Hakaru.Syntax.Nat as N

   -- Pair_
   -- True_ | False_
   -- FromProb_
   -- UnsafeProb_ 
   -- Uniform_
   -- Normal_
   -- VarSym U.Name
   -- Plus

type SymbolTable a = [(Text, Symbol a)]

data Symbol a where
     TLam :: (U.AST a -> Symbol a) -> Symbol a
     TNeu :: U.AST a -> Symbol a

t2 :: (U.AST a -> U.AST a -> U.AST a) -> Symbol a
t2 f = TLam (\ a -> TLam (\b -> TNeu (f a b)))

primTable :: [(Text, Symbol a)]
primTable =  [("Pair",       primPair)
             -- ,("True",       True_)
             -- ,("False",      False_)
             -- ,("fromProb",   FromProb_)
             -- ,("unsafeProb", UnsafeProb_)
             ,("uniform",    primUniform)
             ,("normal",     primNormal)
             ,("+",          primPlus) -- only Nat
             ]

primNormal  = t2 (\x y -> U.MeasureOp_ (U.SealedOp T.Normal) [x,y])
primUniform = t2 (\x y -> U.MeasureOp_ (U.SealedOp T.Normal) [x,y])
primPlus = t2 (\a b -> U.NaryOp_ (Some1 $ T.Sum HSemiring_Nat) [a,b])
primPair = t2 (\a b -> U.Datum_ $ U.SealedDatum $
              U.Datum "pair" (U.Inl $ U.Konst a `U.Et` U.Konst b `U.Et` U.Done))

pVar name = TNeu (U.Var_ (U.Name (N.unsafeNat 0) name))

updateSymbols :: U.Name' -> SymbolTable a -> SymbolTable a
updateSymbols name sym = (name, pVar name) : sym
 

-- figure out symbols and types
symbolResolution :: SymbolTable a -> U.AST' Text -> U.AST' (Symbol a)
symbolResolution symbols ast =
    case ast of
      U.Var name        -> case lookup name symbols of
                             Nothing -> U.Var $ pVar name
                             Just a  -> U.Var a

      U.App f x         -> U.App (symbolResolution symbols f)
                                 (symbolResolution symbols x)

      U.Let name e1 e2  -> U.Let (pVar name)
                                 (symbolResolution symbols e1)
                                 (symbolResolution
                                  (updateSymbols name symbols) e2)

      U.UValue v        -> U.UValue v
                          
      U.Bind name e1 e2 -> U.Bind (pVar name)
                           (symbolResolution symbols e1)
                           (symbolResolution
                            (updateSymbols name symbols) e2)

      _                 -> error "TODO: Add rest of cases"

-- make AST and give unique names for variables

-- | The logic here is to do normalization by evaluation for our
-- primitives. App inspects its first argument to see if it
-- should do something special. Otherwise App behaves as normal.
normAST :: U.AST' (Symbol a) -> U.AST' (Symbol a)
normAST ast =
    case ast of
      U.App (U.Var t) x -> case t of
                            TLam f' ->
                                U.Var $ f' (makeAST x)
                            TNeu e -> (U.Var t)

      U.App f x         -> case normAST f of
                             v@(U.Var _) -> normAST (U.App v x)
                             f'          -> U.App f' x

      U.Bind name e1 e2 -> U.Bind name (normAST e1) (normAST e2)

      v                 -> v

makeAST :: U.AST' (Symbol a) -> U.AST a
makeAST ast =
    case ast of
      U.Var t    -> case t of
                      TLam f' -> error "Wat?"
                      TNeu e  -> e

      U.UValue v -> U.Value_ (U.val v) 

      U.Bind (TNeu (U.Var_ name)) e1 e2 -> U.MBind_ name
                                           (makeAST e1)
                                           (makeAST e2)

      _         -> error "TODO: Add rest of cases"

-- App (App (Var "normal") (UValue (Nat 0))) (UValue (Nat 1))
-- App (Var "normal[0]") (UValue (Nat 1))

data PrimOp' =
     Not'        
   | Impl'       
   | Diff'       
   | Nand'  | Nor'        
   | Pi'        
   | Sin'   | Cos'   | Tan'        
   | Asin'  | Acos'  | Atan'       
   | Sinh'  | Cosh'  | Tanh'       
   | Asinh' | Acosh' | Atanh'      
   | RealPow'    
   | Exp'   | Log'        
   | Infinity'  | NegativeInfinity'
   | GammaFunc' | BetaFunc' 
   | Integrate' | Summate'  
   | Index'    
   | Size'     
   | Reduce'   
   | Equal'     | Less'     
   | NatPow'   
   | Negate'   
   | Abs'      
   | Signum'   
   | Recip'    
   | NatRoot'  
   | Erf'      

data NaryOp' =
     And'
   | Or'
   | Xor'
   | Iff'
   | Min' 
   | Max' 
   | Sum' 
   | Prod'

data MeasureOp' =
     Lebesgue'
   | Counting'
   | Categorical'
   | Uniform'    
   | Normal'     
   | Poisson'    
   | Gamma'      
   | Beta'       
   | DP'         
   | Plate'      
   | Chain'      


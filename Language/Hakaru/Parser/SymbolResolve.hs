{-# LANGUAGE RankNTypes, GADTs, ExistentialQuantification, StandaloneDeriving #-}
module Language.Hakaru.Parser.SymbolResolve where

import Data.List
import Data.Text

import Language.Hakaru.Syntax.DataKind
import qualified Language.Hakaru.Syntax.AST as T
import qualified Language.Hakaru.Parser.AST as U
import Language.Hakaru.Syntax.Sing
import Language.Hakaru.Syntax.IClasses
import qualified Language.Hakaru.Syntax.Nat as N

data Symbol' =
     Pair_
   | True_ | False_
   | FromProb_
   | UnsafeProb_ 
   | Uniform_
   | Normal_
   | VarSym U.Name
   | Plus

type SymbolTable = [(Text, Symbol')]

primTable :: [(Text, Symbol')]
primTable =  [("Pair",       Pair_)
             ,("True",       True_)
             ,("False",      False_)
             ,("fromProb",   FromProb_)
             ,("unsafeProb", UnsafeProb_)
             ,("uniform",    Uniform_)
             ,("normal",     Normal_)
             ,("+",          Plus)
             ]

-- figure out symbols and types
symbolResolution :: SymbolTable -> U.AST' Text -> U.AST' Symbol
symbolResolution symbols ast =
    case ast of
      U.Var name -> case lookup name symbols of
                      Nothing -> VarSym (U.Name name $ N.unsafeNat 0)
                      Just a  -> a
      U.App f x  -> U.App (symbolResolution f)
                          (symbolResolution f)
      _          -> error "TODO: Add rest of cases"

-- make AST and give unique names for variables
makeAST :: U.AST' Symbol' -> U.AST Symbol'
makeAST ast =
    case ast of
      -- U.Var Normal_ -> (\a b -> U.SealedOp T.Normal)
      _             -> error "TODO: Add rest of cases"

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


{-# LANGUAGE RankNTypes, GADTs, ExistentialQuantification, StandaloneDeriving #-}
module Language.Hakaru.Parser.SymbolResolve where

import Data.List
import Data.Text

import Language.Hakaru.Syntax.DataKind hiding (Symbol)
import qualified Language.Hakaru.Syntax.AST as T
import qualified Language.Hakaru.Parser.AST as U
import Language.Hakaru.Syntax.Sing
import Language.Hakaru.Syntax.IClasses
import qualified Language.Hakaru.Syntax.Nat as N

data Symbol =
     Pair_
   | True_ | False_
   | FromProb_
   | UnsafeProb_ 
   | Uniform_
   | Normal_
   | VarSym U.Name
   | Plus

type SymbolTable = [(Text, Symbol)]

primTable :: [(Text, Symbol)]
primTable =  [("Pair",       Pair_)
             ,("True",       True_)
             ,("False",      False_)
             ,("fromProb",   FromProb_)
             ,("unsafeProb", UnsafeProb_)
             ,("uniform",    Uniform_)
             ,("normal",     Normal_)
             ,("+",          Plus)
             ]

updateSymbols :: U.Name' -> SymbolTable -> SymbolTable
updateSymbols name sym = (name,
                          VarSym (U.Name (N.unsafeNat 0) name)) : sym
 

-- figure out symbols and types
symbolResolution :: SymbolTable -> U.AST' Text -> U.AST' Symbol
symbolResolution symbols ast =
    case ast of
      U.Var name       -> case lookup name symbols of
                            Nothing -> U.Var $ VarSym $
                                                U.Name (N.unsafeNat 0) name
                            Just a  -> U.Var a
      U.App f x        -> U.App (symbolResolution symbols f)
                                (symbolResolution symbols f)
      U.Let name e1 e2 -> U.Let name (symbolResolution symbols e1)
                                     (symbolResolution
                                      (updateSymbols name symbols) e2)
      _                -> error "TODO: Add rest of cases"

-- make AST and give unique names for variables
makeAST :: U.AST' Symbol -> U.AST Symbol
makeAST ast =
    case ast of
      --U.Var Normal_ -> (\a b -> U.SealedOp sing T.Normal)
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


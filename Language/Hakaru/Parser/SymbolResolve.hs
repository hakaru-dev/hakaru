{-# LANGUAGE RankNTypes, GADTs, ExistentialQuantification, StandaloneDeriving #-}
module Language.Hakaru.Parser.SymbolResolve where

import Language.Hakaru.Syntax.DataKind
import Language.Hakaru.Syntax.AST (SCon, PrimOp, NaryOp)
import Language.Hakaru.Parser.AST

data Symbol' =
     Fix
   | True' | False'
   | CoerceTo
   | UnsafeFrom 
   | PrimOp
   | NaryOp
   | Array
   | Empty'
   | MeasureOp'
   | MBind
   | Plus

type SymbolTable = [(Text, Symbol')]

primTable :: [(Text, Symbol')]
primTable =  undefined

-- figure out symbols and types
symbolResolution :: SymbolTable -> AST' Text -> AST' Symbol
symbolResolution = undefined

-- make AST and give unique names for variables
makeAST :: AST' Symbol' -> AST Symbol'
makeAST = undefined

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


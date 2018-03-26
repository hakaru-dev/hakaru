{-# LANGUAGE CPP,
             BangPatterns,
             DataKinds,
             FlexibleContexts,
             GADTs,
             KindSignatures,
             ScopedTypeVariables,
             RankNTypes,
             TypeOperators #-}

----------------------------------------------------------------
--                                                    2016.06.23
-- |
-- Module      :  Language.Hakaru.CodeGen.Flatten
-- Copyright   :  Copyright (c) 2016 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  zsulliva@indiana.edu
-- Stability   :  experimental
-- Portability :  GHC-only
--
--   Flatten takes Hakaru ABTs and C vars and returns a CStatement
-- assigning the var to the flattened ABT.
--
----------------------------------------------------------------


module Language.Hakaru.CodeGen.Flatten
  ( flattenABT
  , flattenVar
  , flattenTerm
  , flattenWithName
  , flattenWithName'
  , localVar
  , localVar'
  , opComment
  ) where

import Language.Hakaru.CodeGen.CodeGenMonad
import Language.Hakaru.CodeGen.AST
import Language.Hakaru.CodeGen.Libs
import Language.Hakaru.CodeGen.Types

import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.TypeOf
import Language.Hakaru.Syntax.Datum hiding (Ident)
import Language.Hakaru.Syntax.Reducer
import Language.Hakaru.Syntax.IClasses
import qualified Language.Hakaru.Syntax.Prelude as HKP
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Types.HClasses
import Language.Hakaru.Types.Coercion
import Language.Hakaru.Types.Sing

import           Control.Monad.State.Strict
import           Data.Number.Natural
import           Data.Ratio
import qualified Data.List.NonEmpty as NE
import qualified Data.Sequence      as S
import qualified Data.Foldable      as F
import qualified Data.Traversable   as T


#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative (pure)
import           Control.Monad (replicateM)
import           Data.Functor
import           Data.Monoid        hiding (Product,Sum)
#endif


opComment :: String -> CStat
opComment opStr = CComment $ concat [space," ",opStr," ",space]
  where size  = (50 - (length opStr)) `div` 2 - 8
        space = replicate size '-'

--------------------------------------------------------------------------------
--                                 Top Level                                  --
--------------------------------------------------------------------------------
{-

flattening an ABT will produce a continuation that takes a CExpr representing
a location where the value of the ABT should be stored. Return type of the
the continuation is CodeGen Bool, where the computed bool is whether or not
there is a Reject inside the ABT. Therefore it is only needed when computing
mochastic values

-}

localVar :: Sing (a :: Hakaru) -> CodeGen CExpr
localVar typ = localVar' typ ""

localVar' :: Sing (a :: Hakaru) -> String -> CodeGen CExpr
localVar' typ s =
  do eId <- genIdent' s
     declare typ eId
     return (CVar eId)


flattenWithName'
  :: ABT Term abt
  => abt '[] a
  -> String
  -> CodeGen CExpr
flattenWithName' abt hint = do
  ident <- genIdent' hint
  declare (typeOf abt) ident
  let cvar = CVar ident
  flattenABT abt cvar
  return cvar

flattenWithName
  :: ABT Term abt
  => abt '[] a
  -> CodeGen CExpr
flattenWithName abt = flattenWithName' abt ""

flattenABT
  :: ABT Term abt
  => abt '[] a
  -> (CExpr -> CodeGen ())
flattenABT abt = caseVarSyn abt flattenVar flattenTerm

-- note that variables will find their values in the state of the CodeGen monad
flattenVar
  :: Variable (a :: Hakaru)
  -> (CExpr -> CodeGen ())
flattenVar v = \loc ->
  do v' <- CVar <$> lookupIdent v
     putExprStat $ loc .=. v'

flattenTerm
  :: ABT Term abt
  => Term abt a
  -> (CExpr -> CodeGen ())
-- SCon can contain mochastic terms
flattenTerm (x :$ ys)         = flattenSCon x ys

flattenTerm (NaryOp_ t s)     = flattenNAryOp t s
flattenTerm (Literal_ x)      = flattenLit x
flattenTerm (Empty_ _)        = error "TODO: flattenTerm{Empty}"

flattenTerm (Datum_ d)        = flattenDatum d
flattenTerm (Case_ c bs)      = flattenCase c bs

flattenTerm (Bucket b e rs)   = flattenBucket b e rs

flattenTerm (Array_ s e)      = flattenArray s e
flattenTerm (ArrayLiteral_ s) = flattenArrayLiteral s


---------------------
-- Mochastic Terms --
---------------------
flattenTerm (Superpose_ wes)  = flattenSuperpose wes
flattenTerm (Reject_ _)       = \loc -> putExprStat (mdataWeight loc .=. (intE 0))


--------------------------------------------------------------------------------
--                                  SCon                                      --
--------------------------------------------------------------------------------

flattenSCon
  :: ( ABT Term abt )
  => SCon args a
  -> SArgs abt args
  -> (CExpr -> CodeGen ())

flattenSCon Let_ =
  \(expr :* body :* End) ->
    \loc -> do
      caseBind body $ \v@(Variable _ _ typ) body'->
        do ident <- createIdent v
           declare typ ident
           flattenABT expr (CVar ident)
           flattenABT body' loc

-- Lambdas produce functions and then return a function label exprssion
flattenSCon Lam_ =
  \(body :* End) ->
    \loc ->
      coalesceLambda body $ \args body' ->
        let freevars = fromVarSet . freeVars $ body'
            retTyp   = typeOf body'
        in do { -- create code block and closure structure
                args' <- sequence . foldMap11 argDecl $ args
              ; envId <- genIdent' "env"
              ; fnId  <- genIdent' "fn"
              ; closDataId@(Ident clos_n) <- genIdent' "clos_data"
              ; extDeclare (closureStructure freevars args closDataId retTyp)
              ; funCG (buildType retTyp)
                      fnId
                      ((buildDeclaration (callStruct clos_n) envId):args') $
                  do { putStat (opComment "Begin Unpack Closure")
                       -- need to re-declare variables in functions scope
                     ; mapM_ (\(SomeVariable v@(Variable _ _ typ)) ->
                               lookupIdent v >>= declare typ)
                             freevars
                     ; unpackClosure (CVar envId) cNameStream freevars
                     ; putStat (opComment "End Unpack Closure")
                     ; x <- flattenWithName body'
                     ; putStat . CReturn . Just $ x }

                -- create the closure object
              ; closureId <- genIdent' "closure"
              ; declare' . buildDeclaration (callStruct clos_n) $ closureId
              ; putStat (opComment "Begin Pack Closure")
              ; putExprStat $ ((CVar closureId) ... "_code_ptr") .=. (address (CVar fnId))
              ; packClosure (CVar closureId) cNameStream freevars
              ; putStat (opComment "End Pack Closure")
              ; putExprStat $ loc .=. (CVar closureId) }

  where -- collapses nested lambdas of one argument to lambdas that take a list
        -- arguments
        coalesceLambda
          :: ( ABT Term abt )
          => abt '[x] a
          -> (forall (ys :: [Hakaru]) b. List1 Variable ys -> abt '[] b -> r)
          -> r
        coalesceLambda abt k =
          caseBind abt $ \v abt' ->
            caseVarSyn abt' (const (k (Cons1 v Nil1) abt')) $ \term ->
              case term of
                (Lam_ :$ body :* End) ->
                  coalesceLambda body $ \vars abt'' -> k (Cons1 v vars) abt''
                _ -> k (Cons1 v Nil1) abt'

        argDecl :: Variable (a :: Hakaru) -> [CodeGen CDecl]
        argDecl v@(Variable _ _ typ) =
          [do { ident <- createIdent v ; return (typeDeclaration typ ident) }]

        -- captures the environment variables in closure object
        packClosure, unpackClosure
          :: CExpr
          -> [String]
          -> [SomeVariable (KindOf (a :: Hakaru))]
          -> CodeGen ()
        packClosure _ _      [] = return ()
        packClosure c (n:ns) ((SomeVariable a):as) =
          do { a' <- CVar <$> lookupIdent a
             ; putExprStat $ c ... n .=. a'
             ; packClosure c ns as }
        packClosure _ _ _ = error "this isn't possible"

        unpackClosure _ _      [] = return ()
        unpackClosure c (n:ns) ((SomeVariable a):as) =
          do { a' <- CVar <$> lookupIdent a
             ; putExprStat $ a' .=. c ... n
             ; unpackClosure c ns as }
        unpackClosure _ _ _ = error "this isn't possible"

flattenSCon App_  =
 \(fun :* arg :* End) ->
   \loc ->
     do { closE <- flattenWithName' fun "closure"
        ; paramE <- flattenWithName' arg "param"
        ; putExprStat $ loc .=. CCall (indirect (closE ... "_code_ptr"))
                                      [closE,paramE] }

flattenSCon (PrimOp_ op) = flattenPrimOp op

flattenSCon (ArrayOp_ op) = flattenArrayOp op

flattenSCon (Summate _ sr) =
  \(lo :* hi :* body :* End) ->
    \loc ->
      let  semiTyp = sing_HSemiring sr in
        do loE <- flattenWithName' lo "lo"
           hiE <- flattenWithName' hi "hi"

           putStat $ opComment "Begin Summate"

           case semiTyp of
             -- special prob branch
             SProb -> do
               summateArrId <- genIdent' "summate_arr"
               declare (SArray SProb) summateArrId
               let summateArrE = CVar summateArrId
               putExprStat $ arraySize summateArrE .=. (hiE .-. loE)
               putExprStat $ arrayData summateArrE
                     .=. (castToPtrOf [CDouble]
                           (mallocE ((arraySize summateArrE) .*.
                                    (CSizeOfType (CTypeName [CDouble] False)))))
               lseSummateArrayCG body summateArrE loc
               putExprStat $ freeE (arrayData summateArrE)

             _ ->
               caseBind body $ \v body' -> do
                 iterI <- createIdent v
                 declare SNat iterI

                 accI <- genIdent' "acc"
                 declare semiTyp accI
                 assign accI (case semiTyp of
                                SReal -> floatE 0
                                _     -> intE 0)

                 let accVar  = CVar accI
                     iterVar = CVar iterI

                 reductionCG (Left CAddOp)
                             accVar
                             (iterVar .=. loE)
                             (iterVar .<. hiE)
                             (CUnary CPostIncOp iterVar) $
                   (putExprStat . (accVar .+=.) =<< flattenWithName body')
                 putExprStat $ loc .=. accVar

           putStat $ opComment "End Summate"



flattenSCon (Product _ sr) =
  \(lo :* hi :* body :* End) ->
    \loc ->
      let  semiTyp = sing_HSemiring sr in
        do loE <- flattenWithName' lo "lo"
           hiE <- flattenWithName' hi "hi"

           putStat $ opComment "Begin Product"

           case semiTyp of
           -- special prob branch
             SProb -> kahanSummationCG body loE hiE loc

             _ ->
               caseBind body $ \v body' -> do
                 iterI <- createIdent v
                 declare SNat iterI

                 accI <- genIdent' "acc"
                 declare semiTyp accI
                 assign accI (case semiTyp of
                                SReal -> floatE 1
                                _     -> intE 1)

                 let accVar  = CVar accI
                     iterVar = CVar iterI

                 reductionCG (Left CMulOp)
                             accVar
                             (iterVar .=. loE)
                             (iterVar .<. hiE)
                             (CUnary CPostIncOp iterVar) $
                    (putExprStat . (accVar .*=.) =<< flattenWithName body')
                 putExprStat (loc .=. accVar)
           putStat $ opComment "End Product"


--------------------
-- SCon Coercions --
--------------------
{- Helpers found by searching "Coercion Helpers" -}

flattenSCon (CoerceTo_ ctyp) =
  \(e :* End) ->
    \loc ->
      do eE <- flattenWithName e
         cE <- coerceToCG ctyp eE
         putExprStat $ loc .=. cE

flattenSCon (UnsafeFrom_ ctyp) =
  \(e :* End) ->
    \loc ->
      do eE <- flattenWithName e
         cE <- coerceFromCG ctyp eE
         putExprStat $ loc .=. cE

-----------------------------------
-- SCons in the Stochastic Monad --
-----------------------------------

flattenSCon (MeasureOp_ op) = flattenMeasureOp op

flattenSCon Dirac           =
  \(e :* End) ->
    \loc ->
      do sE <- flattenWithName' e "samp"
         putExprStat $ mdataWeight loc .=. (floatE 0)
         putExprStat $ mdataSample loc .=. sE

flattenSCon MBind           =
  \(ma :* b :* End) ->
    \loc ->
      caseBind b $ \v@(Variable _ _ typ) mb ->
        do -- first
           mE <- flattenWithName' ma "m"

           -- assign that sample to var
           vId <- createIdent v
           declare typ vId
           assign vId (mdataSample mE)
           flattenABT mb loc
           putExprStat $ mdataWeight loc .+=. (mdataWeight mE)

-- for now plats make use of a global sample
flattenSCon Plate           =
  \(size :* b :* End) ->
    \loc ->
      caseBind b $ \v body ->
        do sizeE <- flattenWithName' size "s"
           isMM <- managedMem <$> get
           when (not isMM) (error "plate will leak memory without the '-g' flag and boehm-gc")
           putExprStat $ (arraySize . mdataSample $ loc) .=. sizeE
           putMallocStat (arrayData . mdataSample $ loc) sizeE (typeOf body)

           weightId <- genIdent' "w"
           declare SProb weightId
           let weightE = CVar weightId
           assign weightId (floatE 0)

           itId <- createIdent v
           declare SNat itId
           let itE = CVar itId
               currInd  = index (arrayData . mdataSample $ loc) itE

           sampId <- genIdent' "samp"
           declare (typeOf $ body) sampId
           let sampE = CVar sampId

           reductionCG (Left CAddOp)
                       weightE
                       (itE .=. (intE 0))
                       (itE .<. sizeE)
                       (CUnary CPostIncOp itE)
                       (do flattenABT body sampE
                           putExprStat (currInd .=. (mdataSample sampE))
                           putExprStat (weightE .+=. (mdataWeight sampE)))

           putExprStat $ mdataWeight loc .=. weightE

-----------------------------------
-- SCon's that arent implemented --
-----------------------------------

flattenSCon x               = \_ -> \_ -> error $ "TODO: flattenSCon: " ++ show x



--------------------------------------------------------------------------------
--                                 NaryOps                                    --
--------------------------------------------------------------------------------

flattenNAryOp :: ABT Term abt
              => NaryOp a
              -> S.Seq (abt '[] a)
              -> (CExpr -> CodeGen ())
flattenNAryOp op args =
  \loc ->
    do es <- T.mapM flattenWithName args
       case op of
         And -> boolNaryOp op es loc
         Or  -> boolNaryOp op es loc
         Xor -> boolNaryOp op es loc
         Iff -> boolNaryOp op es loc
         (Sum HSemiring_Prob) -> logSumExpCG es loc
         _ -> let opE = F.foldr (binaryOp op) (S.index es 0) (S.drop 1 es)
              in  putExprStat (loc .=. opE)

  where boolNaryOp op' es' loc' =
          let indexOf x = CMember x (Ident "index") True
              es''      = fmap indexOf es'
              expr      = F.foldr (binaryOp op')
                                  (S.index es'' 0)
                                  (S.drop 1 es'')
          in  putExprStat ((indexOf loc') .=. expr)


--------------------------------------------------------------------------------
--                                  Literals                                  --
--------------------------------------------------------------------------------

flattenLit
  :: Literal a
  -> (CExpr -> CodeGen ())
flattenLit lit =
  \loc ->
    case lit of
      (LNat x)  -> putExprStat $ loc .=. (intE $ fromIntegral x)
      (LInt x)  -> putExprStat $ loc .=. (intE x)
      (LReal x) -> putExprStat $ loc .=. (floatE $ fromRational x)
      (LProb x) -> let rat = fromNonNegativeRational x
                       x'  = (fromIntegral $ numerator rat)
                           / (fromIntegral $ denominator rat)
                       xE  = log1pE (floatE x' .-. intE 1)
                   in putExprStat (loc .=. xE)

--------------------------------------------------------------------------------
--                                Array and ArrayOps                          --
--------------------------------------------------------------------------------


flattenArray
  :: (ABT Term abt)
  => (abt '[] 'HNat)
  -> (abt '[ 'HNat ] a)
  -> (CExpr -> CodeGen ())
flattenArray arity body =
  \loc ->
    caseBind body $ \v body' -> do
      let arityE = arraySize loc
          dataE  = arrayData loc
          typ    = typeOf body'

      flattenABT arity arityE

      isManagedMem <- managedMem <$> get
      let malloc' = if isManagedMem then gcMalloc else mallocE
      putExprStat $   dataE
                  .=. (CCast (CTypeName (buildType typ) True)
                             (malloc' (arityE .*. (CSizeOfType (CTypeName (buildType typ) False)))))

      itId  <- createIdent v
      declare SNat itId
      let itE     = CVar itId
          currInd = index dataE itE

      putStat $ opComment "Begin Array"
      forCG (itE .=. (intE 0))
            (itE .<. arityE)
            (CUnary CPostIncOp itE)
            (flattenABT body' currInd)
      putStat $ opComment "End Array"

flattenArrayLiteral
  :: ( ABT Term abt )
  => [abt '[] a]
  -> (CExpr -> CodeGen ())
flattenArrayLiteral es =
  \loc -> do
    arrId <- genIdent
    isManagedMem <- managedMem <$> get
    let arity = fromIntegral . length $ es
        typ   = typeOf . head $ es
        arrE = CVar arrId
        malloc' = if isManagedMem then gcMalloc else mallocE

    declare (SArray typ) arrId
    putExprStat $   (arrayData arrE)
                .=. (CCast (CTypeName (buildType typ) True)
                           (malloc' ((intE arity) .*. (CSizeOfType (CTypeName (buildType typ) False)))))

    putExprStat $ arraySize arrE .=. (intE arity)
    sequence_ . snd $ foldl (\(i,acc) e -> (succ i,(assignIndex e i arrE):acc))
                            (0,[])
                            es
    putExprStat $ loc .=. arrE
  where assignIndex
          :: ( ABT Term abt )
          => abt '[] a
          -> Integer
          -> (CExpr -> CodeGen ())
        assignIndex e i loc = do
          eE <- flattenWithName e
          putExprStat $ indirect ((arrayData loc) .+. (intE i)) .=. eE

--------------
-- ArrayOps --
--------------

flattenArrayOp
  :: ( ABT Term abt
     , typs ~ UnLCs args
     , args ~ LCs typs
     )
  => ArrayOp typs a
  -> SArgs abt args
  -> (CExpr -> CodeGen ())


flattenArrayOp (Index _)  =
  \(arr :* ind :* End) ->
    \loc ->
      do indE <- flattenWithName ind
         arrE <- flattenWithName arr
         let valE = index (CMember arrE (Ident "data") True) indE
         putExprStat (loc .=. valE)

flattenArrayOp (Size _)   =
  \(arr :* End) ->
    \loc ->
      do arrE <- flattenWithName arr
         putExprStat (loc .=. (CMember arrE (Ident "size") True))

flattenArrayOp (Reduce _) = error "TODO: flattenArrayOp"
  -- \(fun :* base :* arr :* End) ->
  -- do funE  <- flattenABT fun
  --    baseE <- flattenABT base
  --    arrE  <- flattenABT arr
  --    accI  <- genIdent' "acc"
  --    iterI <- genIdent' "iter"

  --    let sizeE = CMember arrE (Ident "size") True
  --        iterE = CVar iterI
  --        accE  = CVar accI
  --        cond  = iterE .<. sizeE
  --        inc   = CUnary CPostIncOp iterE

  --    declare (typeOf base) accI
  --    declare SInt iterI
  --    assign accI baseE
  --    forCG (iterE .=. (intE 0)) cond inc $
  --      assign accI $ CCall funE [accE]

  --    return accE

--------------------------------------------------------------------------------
--                              Bucket and Reducers                           --
--------------------------------------------------------------------------------
{- Declarations for buckets -
  since we will have some product of monoids we need unique names for each one.

  Ex:
    bucket i from 0 to 100:
      fanout(add(\_ -> 1),add(\_ -> 2))

  we will need to keep track of two ints:

  int x;
  int y;
  for (i = 0; i < 100; i++) {
    x += 1;
    y += 2;
  }

  Summary objects are nested pairs, e.g. pair(nat,pair(real,array(nat)))
-}

flattenBucket
  :: (ABT Term abt)
  => abt '[] 'HNat
  -> abt '[] 'HNat
  -> Reducer abt '[] a
  -> (CExpr -> CodeGen ())
flattenBucket lo hi red = \loc -> do
    putStat $ opComment "Begin Bucket"
    loE <- flattenWithName' lo "lo"
    hiE <- flattenWithName' hi "hi"
    itId <- genIdent' "it"
    declare SNat itId
    let itE = CVar itId
    initRed red loc
    isPar <- sharedMem <$> get
    -- declare special functions for combining threads. This doesn't completely
    -- work now, because these need to capture free variables.
    reductionCG (Right ( typeOfReducer red
                       , \e -> seqDo (  initRed red (indirect e)
                                     >> putStat (CReturn Nothing))
                       , \a b -> seqDo (  mulRed red (indirect a) (indirect b)
                                       >> putStat (CReturn Nothing))))
                loc
                (itE .=. loE)
                (itE .<. hiE)
                (CUnary CPostIncOp itE)
                (accumRed isPar red itE loc)
    putStat $ opComment "End Bucket"

  where initRed
          :: (ABT Term abt)
          => Reducer abt xs a
          -> (CExpr -> CodeGen ())
        initRed mr = \loc ->
          case mr of
            (Red_Fanout mr1 mr2) -> initRed mr1 (datumFst loc)
                                 >> initRed mr2 (datumSnd loc)
            (Red_Split _ mr1 mr2) -> initRed mr1 (datumFst loc)
                                  >> initRed mr2 (datumSnd loc)
            (Red_Index s _ body) ->
              let (vs,s') = caseBinds s
                  btyp     = typeOfReducer body in
                do sequence_ . foldMap11
                     (\v' -> case v' of
                       (Variable _ _ typ') ->
                         [declare typ' =<< createIdent v'])
                     $ vs
                   sE <- flattenWithName' s' "red_size"
                   putExprStat $ arraySize loc .=. sE
                   putMallocStat (arrayData loc) sE btyp
                   itId  <- genIdent
                   declare SNat itId
                   let itE = CVar itId
                   forCG (itE .=. (intE 0))
                         (itE .<. sE)
                         (CUnary CPostIncOp itE)
                         (initRed body (index (arrayData loc) itE))
            Red_Nop -> return ()
            (Red_Add sr _) ->
              putExprStat $ loc .=. (addMonoidIdentity . sing_HSemiring $ sr)

        accumRed
          :: (ABT Term abt)
          => Bool
          -> Reducer abt xs a
          -> CExpr
          -> (CExpr -> CodeGen ())
        accumRed isPar mr itE = \loc ->
          case mr of
            (Red_Index _ a body) ->
              caseBind a $ \v@(Variable _ _ typ) a' ->
                let (vs,a'') = caseBinds a' in
                  do vId <- createIdent v
                     declare typ vId
                     putExprStat $ (CVar vId) .=. itE
                     sequence_ . foldMap11
                       (\v' -> case v' of
                         (Variable _ _ typ') ->
                           [declare typ' =<< createIdent v'])
                       $ vs
                     aE <- flattenWithName' a'' "index"
                     accumRed isPar body itE (index (arrayData loc) aE)
            (Red_Fanout mr1 mr2) -> accumRed isPar mr1 itE (datumFst loc)
                                 >> accumRed isPar mr2 itE (datumSnd loc)
            (Red_Split b mr1 mr2) ->
              caseBind b $ \v@(Variable _ _ typ) b' ->
                let (vs,b'') = caseBinds b' in
                  do vId <- createIdent v
                     declare typ vId
                     putExprStat $ (CVar vId) .=. itE
                     sequence_ . foldMap11
                       (\v' -> case v' of
                         (Variable _ _ typ') ->
                           [declare typ' =<< createIdent v'])
                       $ vs
                     bE <- flattenWithName' b'' "cond"
                     ifCG (bE ... "index" .==. (intE 0))
                          (accumRed isPar mr1 itE (datumFst loc))
                          (accumRed isPar mr2 itE (datumSnd loc))
            Red_Nop -> return ()
            (Red_Add sr e) ->
              caseBind e $ \v@(Variable _ _ typ) e' ->
                let (vs,e'') = caseBinds e' in
                  do vId <- createIdent v
                     declare typ vId
                     putExprStat $ (CVar vId) .=. itE
                     sequence_ . foldMap11
                       (\v' -> case v' of
                         (Variable _ _ typ') ->
                           [declare typ' =<< createIdent v'])
                       $ vs
                     eE <- flattenWithName e''
                     -- when isPar $  putStat . CPPStat . ompToPP $ OMP Critical
                     case sing_HSemiring sr of
                       SProb -> logSumExpCG (S.fromList [loc,eE]) loc
                       _ -> putExprStat $ loc .+=. eE

        mulRed
          :: (ABT Term abt)
          => Reducer abt xs a
          -> (CExpr -> CExpr -> CodeGen ())
        mulRed mr outp inp =
          case mr of
             (Red_Index _ _ mr') ->
               do itE <- localVar SNat
                  forCG (itE .=. (intE 0))
                        (itE .<. (intE 0))
                        (CUnary CPostIncOp itE)
                        (mulRed mr'
                                (index (arrayData outp) itE)
                                (index (arrayData inp) itE))
             (Red_Fanout mr1 mr2) -> mulRed mr1 (datumFst outp) (datumFst inp)
                                  >> mulRed mr2 (datumFst outp) (datumFst inp)
             (Red_Split _ mr1 mr2) -> mulRed mr1 (datumFst outp) (datumFst inp)
                                   >> mulRed mr2 (datumFst outp) (datumFst inp)
             Red_Nop -> return ()
             (Red_Add _ _) -> putExprStat $ outp .+=. inp

addMonoidIdentity :: Sing (a :: Hakaru) -> CExpr
addMonoidIdentity s =
  case s of
    SNat  -> intE 0
    SInt  -> intE 0
    SReal -> floatE 0
    SProb -> logE (floatE 0)
    SArray x -> addMonoidIdentity x
    x -> error $ "addMonoidIdentity{" ++ show x ++ "}"

--------------------------------------------------------------------------------
--                                 Datum and Case                             --
--------------------------------------------------------------------------------
{-

Datum are sums of products of types. This maps to a C structure. flattenDatum
will produce a literal of some datum type. This will also produce a global
struct representing that datum which will be needed for the C compiler.

-}


flattenDatum
  :: (ABT Term abt)
  => Datum (abt '[]) (HData' a)
  -> (CExpr -> CodeGen ())
flattenDatum (Datum _ typ code) =
  \loc ->
    do extDeclareTypes typ
       assignDatum code loc

assignDatum
  :: (ABT Term abt)
  => DatumCode xss (abt '[]) c
  -> CExpr
  -> CodeGen ()
assignDatum code ident =
  let ind       = getIndex code
      indExpr = CMember ident (Ident "index") True
  in  do putExprStat (indExpr .=. (intE ind))
         sequence_ $ assignSum code ident
  where getIndex :: DatumCode xss b c -> Integer
        getIndex (Inl _)    = 0
        getIndex (Inr rest) = succ (getIndex rest)

assignSum
  :: (ABT Term abt)
  => DatumCode xs (abt '[]) c
  -> CExpr
  -> [CodeGen ()]
assignSum code ident = fst $ runState (assignSum' code ident) cNameStream

assignSum'
  :: (ABT Term abt)
  => DatumCode xs (abt '[]) c
  -> CExpr
  -> State [String] [CodeGen ()]
assignSum' (Inr rest) topIdent =
  do (_:names) <- get
     put names
     assignSum' rest topIdent
assignSum' (Inl prod) topIdent =
  do (name:_) <- get
     return $ assignProd prod topIdent (CVar . Ident $ name)

assignProd
  :: (ABT Term abt)
  => DatumStruct xs (abt '[]) c
  -> CExpr
  -> CExpr
  -> [CodeGen ()]
assignProd dstruct topIdent sumIdent =
  fst $ runState (assignProd' dstruct topIdent sumIdent) cNameStream

assignProd'
  :: (ABT Term abt)
  => DatumStruct xs (abt '[]) c
  -> CExpr
  -> CExpr
  -> State [String] [CodeGen ()]
assignProd' Done _ _ = return []
assignProd' (Et (Konst d) rest) topIdent (CVar sumIdent) =
  do (name:names) <- get
     put names
     let varName  = CMember (CMember (CMember topIdent
                                              (Ident "sum")
                                              True)
                                     sumIdent
                                     True)
                            (Ident name)
                            True
     rest' <- assignProd' rest topIdent (CVar sumIdent)
     return $ [flattenABT d varName] ++ rest'

assignProd' _ _ _  = error $ "TODO: assignProd Ident"


----------
-- Case --
----------

-- currently we can only match on boolean values
flattenCase
  :: forall abt a b
  .  (ABT Term abt)
  => abt '[] a
  -> [Branch a abt b]
  -> (CExpr -> CodeGen ())

flattenCase c [ Branch (PDatum _ (PInl PDone))        trueB
              , Branch (PDatum _ (PInr (PInl PDone))) falseB ] =
  \loc ->
    do cE <- flattenWithName c
       ifCG ((cE ... "index") .==. (intE 0))
            (flattenABT trueB  loc)
            (flattenABT falseB loc)

flattenCase e [ Branch (PDatum _ (PInl (PEt (PKonst PVar)
                                            (PEt (PKonst PVar)
                                                 PDone)))) b
              ]
  = \loc -> do
    eE <- flattenWithName e
    caseBind b $ \vfst@(Variable _ _ fstTyp) b' ->
      caseBind b' $ \vsnd@(Variable _ _ sndTyp) b'' -> do
        fstId <- createIdent vfst
        sndId <- createIdent vsnd
        declare fstTyp fstId
        declare sndTyp sndId
        putExprStat $ (CVar fstId) .=. (datumFst eE)
        putExprStat $ (CVar sndId) .=. (datumSnd eE)
        flattenABT b'' loc

flattenCase e _ = error $ "TODO: flattenCase{" ++ show (typeOf e) ++ "}"


--------------------------------------------------------------------------------
--                                     PrimOp                                 --
--------------------------------------------------------------------------------

flattenPrimOp
  :: ( ABT Term abt
     , typs ~ UnLCs args
     , args ~ LCs typs)
  => PrimOp typs a
  -> SArgs abt args
  -> (CExpr -> CodeGen ())


flattenPrimOp Pi =
  \End ->
    \loc -> let piE = log1pE ((CVar . Ident $ "M_PI") .-. (intE 1)) in
      putExprStat (loc .=. piE)

flattenPrimOp Not =
  \(a :* End) ->
    \loc ->
      do aE <- flattenWithName a
         bId <- genIdent
         declare (typeOf a) bId
         let bE = CVar bId
         putExprStat $ datumIndex bE .=. (CCond (datumIndex aE .==. (intE 1))
                                               (intE 0)
                                               (intE 1))
         putExprStat $ loc .=. bE

flattenPrimOp RealPow =
  \(base :* power :* End) ->
    \loc ->
      do baseE <- flattenWithName base
         powerE <- flattenWithName power
         let realPow = CCall (CVar . Ident $ "pow")
                             [ expm1E baseE .+. (intE 1), powerE]
         putExprStat $ loc .=. (log1pE (realPow .-. (intE 1)))

flattenPrimOp (NatPow baseTyp) =
  \(base :* power :* End) ->
    \loc ->
      let sBase = sing_HSemiring baseTyp in
      do baseId <- genIdent
         declare sBase baseId
         let baseE = CVar baseId
         flattenABT base baseE
         powerE <- flattenWithName power
         let powerOf x y = CCall (CVar . Ident $ "pow") [x,y]
             value = case sBase of
                       SProb -> log1pE $ (powerOf (expm1E baseE .+. (intE 1)) powerE)
                                  .-. (intE 1)
                       _     -> powerOf baseE powerE
         putExprStat $ loc .=. value

flattenPrimOp (NatRoot baseTyp) =
  \(base :* root :* End) ->
    \loc ->
      let sBase = sing_HRadical baseTyp in
      do baseId <- genIdent
         declare sBase baseId
         let baseE = CVar baseId
         flattenABT base baseE
         rootE <- flattenWithName root
         let powerOf x y = CCall (CVar . Ident $ "pow") [x,y]
             recipE = (floatE 1) ./. rootE
             value = case sBase of
                       SProb -> log1pE $ (powerOf (expm1E baseE .+. (intE 1)) recipE)
                                      .-. (intE 1)
                       _     -> powerOf baseE recipE
         putExprStat $ loc .=. value

flattenPrimOp (Recip t) =
  \(a :* End) ->
    \loc ->
      do aE <- flattenWithName a
         case t of
           HFractional_Real -> putExprStat $ loc .=. ((intE 1) ./. aE)
           HFractional_Prob -> putExprStat $ loc .=. (CUnary CMinOp aE)

-- | exp : real -> prob, because of this we can just turn it into a prob without taking
--   its log, which would give us an exp in the log-domain
flattenPrimOp Exp = \(a :* End) -> flattenABT a

flattenPrimOp (Equal _) =
  \(a :* b :* End) ->
    \loc ->
      do aE <- flattenWithName a
         bE <- flattenWithName b

         -- special case for booleans
         let aE' = case (typeOf a) of
                     (SData _ (SPlus SDone (SPlus SDone SVoid))) -> (CMember aE (Ident "index") True)
                     _ -> aE
         let bE' = case (typeOf b) of
                     (SData _ (SPlus SDone (SPlus SDone SVoid))) -> (CMember bE (Ident "index") True)
                     _ -> bE

         putExprStat $   (CMember loc (Ident "index") True)
                     .=. (CCond (aE' .==. bE') (intE 0) (intE 1))


flattenPrimOp (Less _) =
  \(a :* b :* End) ->
    \loc ->
      do aE <- flattenWithName a
         bE <- flattenWithName b
         putExprStat $ (CMember loc (Ident "index") True)
                     .=. (CCond (aE .<. bE) (intE 0) (intE 1))

flattenPrimOp (Negate _) =
 \(a :* End) ->
   \loc ->
     do aE <- flattenWithName a
        putExprStat $ loc .=. (CUnary CMinOp $ aE)

flattenPrimOp t  = \_ -> error $ "TODO: flattenPrimOp: " ++ show t

flattenPrimOp Choose = \(a :* b :* End) -> error $ "TODO: flattenPrimOp: choose"

--------------------------------------------------------------------------------
--                           MeasureOps and Superpose                         --
--------------------------------------------------------------------------------

{-

The sections contains operations in the stochastic monad. See also
(Dirac, MBind, and Plate) found in SCon. Also see Reject found at the top level.

Remember in the C runtime. Measures are housed in a measure function, which
takes an `struct mdata` location. The MeasureOp attempts to store a value at
that location and returns 0 if it fails and 1 if it succeeds in that task.

The functions uniformCG, normalCG, and gammaCG are primitives that will generate
functions and call them (similar to logSumExpCG). The reduce code size and make
samplers a little more readable.

TODO: add inline pragmas to uniformCG, normalCG, and gammaCG
-}

uniformFun :: CFunDef
uniformFun = CFunDef (CTypeSpec <$> retTyp)
                     (CDeclr Nothing (CDDeclrIdent funcId))
                     [typeDeclaration SReal loId
                     ,typeDeclaration SReal hiId]
                     (CCompound . concat
                     $ [ CBlockDecl <$> [declMD]
                       , CBlockStat <$> comment ++ [assW,assS,CReturn . Just $ mE]]
                     )
  where r          = castTo [CDouble] randE
        rMax       = castTo [CDouble] (CVar . Ident $ "RAND_MAX")
        retTyp     = buildType (SMeasure SReal)
        (mId,mE)   = let ident = Ident "mdata" in (ident,CVar ident)
        (loId,loE) = let ident = Ident "lo" in (ident,CVar ident)
        (hiId,hiE) = let ident = Ident "hi" in (ident,CVar ident)
        value      = (loE .+. ((r ./. rMax) .*. (hiE .-. loE)))
        comment = fmap CComment
          ["uniform :: real -> real -> *(mdata real) -> ()"
          ,"------------------------------------------------"]
        declMD     = buildDeclaration (head retTyp) mId
        assW       = CExpr . Just $ mdataWeight mE .=. (floatE 0)
        assS       = CExpr . Just $ mdataSample mE .=. value
        funcId     = Ident "uniform"


uniformCG :: CExpr -> CExpr -> (CExpr -> CodeGen ())
uniformCG aE bE =
  \loc -> do
    uId <- reserveIdent "uniform"
    extDeclareTypes (SMeasure SReal)
    extDeclare . CFunDefExt $ uniformFun
    putExprStat $ loc .=. CCall (CVar uId) [aE,bE]


{-
  This is very cryptic, but I assure you it is only building an AST for the
  Marsaglia Polar Method
-}

normalFun :: CFunDef
normalFun = CFunDef (CTypeSpec <$> retTyp)
                    (CDeclr Nothing (CDDeclrIdent (Ident "normal")))
                    [typeDeclaration SReal aId
                    ,typeDeclaration SProb bId ]
                    ( CCompound . concat
                    $ [[CBlockDecl declMD],comment,decls,stmts])

  where r      = castTo [CDouble] randE
        rMax   = castTo [CDouble] (CVar . Ident $ "RAND_MAX")
        retTyp = buildType (SMeasure SReal)
        (aId,aE) = let ident = Ident "a" in (ident,CVar ident)
        (bId,bE) = let ident = Ident "b" in (ident,CVar ident)
        (qId,qE) = let ident = Ident "q" in (ident,CVar ident)
        (uId,uE) = let ident = Ident "u" in (ident,CVar ident)
        (vId,vE) = let ident = Ident "v" in (ident,CVar ident)
        (rId,rE) = let ident = Ident "r" in (ident,CVar ident)
        (mId,mE) = let ident = Ident "mdata" in (ident,CVar ident)
        declMD     = buildDeclaration (head retTyp) mId
        draw xE = CExpr . Just $ xE .=. (((r ./. rMax) .*. (floatE 2)) .-. (floatE 1))
        body = seqCStat [draw uE
                        ,draw vE
                        ,CExpr . Just $ qE .=. ((uE .*. uE) .+. (vE .*. vE))]
        polar = CWhile (qE .>. (floatE 1)) body True
        setR  = CExpr . Just $ rE .=. (sqrtE (((CUnary CMinOp (floatE 2)) .*. logE qE) ./. qE))
        finalValue = aE .+. (uE .*. rE .*. bE)
        comment = fmap (CBlockStat . CComment)
          ["normal :: real -> real -> *(mdata real) -> ()"
          ,"Marsaglia Polar Method"
          ,"-----------------------------------------------"]
        decls = (CBlockDecl . typeDeclaration SReal) <$> [uId,vId,qId,rId]
        stmts = CBlockStat <$> [polar,setR, assW, assS,CReturn . Just $ mE]
        assW = CExpr . Just $ mdataWeight mE .=. (floatE 0)
        assS = CExpr . Just $ mdataSample mE .=. finalValue


normalCG :: CExpr -> CExpr -> (CExpr -> CodeGen ())
normalCG aE bE =
  \loc -> do
    nId <- reserveIdent "normal"
    extDeclareTypes (SMeasure SReal)
    extDeclare . CFunDefExt $ normalFun
    putExprStat $ loc .=. (CCall (CVar nId) [aE,bE])

{-
  This method is from Marsaglia and Tsang "a simple method for generating gamma variables"
-}
gammaFun :: CFunDef
gammaFun = CFunDef (CTypeSpec <$> retTyp)
                   (CDeclr Nothing (CDDeclrIdent (Ident "gamma")))
                   [typeDeclaration SProb aId
                   ,typeDeclaration SProb bId]
                    ( CCompound . concat
                    $ [[CBlockDecl declMD],comment,decls,stmts])
  where (aId,aE) = let ident = Ident "a" in (ident,CVar ident)
        (bId,bE) = let ident = Ident "b" in (ident,CVar ident)
        (cId,cE) = let ident = Ident "c" in (ident,CVar ident)
        (dId,dE) = let ident = Ident "d" in (ident,CVar ident)
        (xId,xE) = let ident = Ident "x" in (ident,CVar ident)
        (vId,vE) = let ident = Ident "v" in (ident,CVar ident)
        (uId,uE) = let ident = Ident "u" in (ident,CVar ident)
        (mId,mE) = let ident = Ident "mdata" in (ident,CVar ident)
        retTyp = buildType (SMeasure SProb)
        declMD     = buildDeclaration (head retTyp) mId
        comment = fmap (CBlockStat . CComment)
          ["gamma :: real -> prob -> *(mdata prob) -> ()"
          ,"Marsaglia and Tsang 'a simple method for generating gamma variables'"
          ,"--------------------------------------------------------------------"]
        decls = fmap CBlockDecl $ (fmap (typeDeclaration SReal) [dId,cId,vId])
                               ++ (fmap (typeDeclaration (SMeasure SReal)) [uId,xId])
        stmts = fmap CBlockStat $ [assD,assC,outerWhile]
        xS = mdataSample xE
        uS = mdataSample uE
        assD = CExpr . Just $ dE .=. (aE .-. ((floatE 1) ./. (floatE 3)))
        assC = CExpr . Just $ cE .=. ((floatE 1) ./. (sqrtE ((floatE 9) .*. dE)))
        outerWhile = CWhile (intE 1) (seqCStat [innerWhile,assV,assU,exit]) False
        innerWhile = CWhile (vE .<=. (floatE 0)) (seqCStat [assX,assVIn]) True
        assX = CExpr . Just $ xE .=. (CCall (CVar . Ident $ "normal") [(floatE 0),(floatE 1)])
        assVIn = CExpr . Just $ vE .=. ((floatE 1) .+. (cE .*. xS))
        assV = CExpr . Just $ vE .=. (vE .*. vE .*. vE)
        assU = CExpr . Just $ uE .=. (CCall (CVar . Ident $ "uniform") [(floatE 0),(floatE 1)])
        exitC1 = uS .<. ((floatE 1) .-. ((floatE 0.331 .*. (xS .*. xS) .*. (xS .*. xS))))
        exitC2 = (logE uS) .<. (((floatE 0.5) .*. (xS .*. xS)) .+. (dE .*. ((floatE 1.0) .-. vE .+. (logE vE))))
        assW = CExpr . Just $ mdataWeight mE .=. (floatE 0)
        assS = CExpr . Just $ mdataSample mE .=. (logE (dE .*. vE)) .+. bE
        exit = CIf (exitC1 .||. exitC2) (seqCStat [assW,assS,CReturn . Just $ mE]) Nothing


gammaCG :: CExpr -> CExpr -> (CExpr -> CodeGen ())
gammaCG aE bE =
  \loc -> do
     extDeclareTypes (SMeasure SReal)
     (_:_:gId:[]) <- mapM reserveIdent ["uniform","normal","gamma"]
     mapM_ (extDeclare . CFunDefExt) [uniformFun,normalFun,gammaFun]
     putExprStat $ loc .=. (CCall (CVar gId) [aE,bE])


flattenMeasureOp
  :: forall abt typs args a .
     ( ABT Term abt
     , typs ~ UnLCs args
     , args ~ LCs typs )
  => MeasureOp typs a
  -> SArgs abt args
  -> (CExpr -> CodeGen ())


flattenMeasureOp Uniform =
  \(a :* b :* End) ->
    \loc ->
      do aE <- flattenWithName a
         bE <- flattenWithName b
         uniformCG aE bE loc


flattenMeasureOp Normal  =
  \(a :* b :* End) ->
    \loc ->
      do aE <- flattenWithName a
         bE <- flattenWithName b
         normalCG aE (expE bE) loc

flattenMeasureOp Poisson =
  \(lam :* End) ->
    \loc ->
      do lamE <- flattenWithName lam
         (lId:kId:pId:[]) <- mapM genIdent' ["l","k","p"]
         declare SProb lId
         declare SNat  kId
         declare SProb pId
         let (lE:kE:pE:[]) = fmap CVar [lId,kId,pId]
         putExprStat $ lE .=. (expE (CUnary CMinOp $ expE lamE))
         putExprStat $ kE .=. (intE 0)
         putExprStat $ pE .=. (floatE 1)
         doWhileCG (pE .>. lE) $
           do uId <- genIdent' "u"
              declare (SMeasure SReal) uId
              let uE = CVar uId
              uniformCG (intE 0) (intE 1) uE
              putExprStat $ pE .*=. (mdataSample uE)
              putExprStat $ kE .+=. (intE 1)

         putExprStat $ mdataWeight loc .=. (intE 0)
         putExprStat $ mdataSample loc .=. (kE .-. (intE 1))

flattenMeasureOp Gamma =
  \(a :* b :* End) ->
    \loc ->
      do aE <- flattenWithName a
         bE <- flattenWithName b
         gammaCG (expE aE) bE loc


flattenMeasureOp Beta =
  \(a :* b :* End) -> flattenABT (HKP.beta'' a b)


-- I ran into a bug here where sometime I recieved a location by reference and
-- others by value. Since measureOps assign a sample to mdata that they have a
-- reference to, we should enforce that when passing around mdata it is by
-- reference
flattenMeasureOp Categorical = \(arr :* End) ->
  \loc ->
    do arrE <- flattenWithName arr

       itId <- genIdent' "it"
       declare SNat itId
       let itE = CVar itId

       -- Accumulator for the total probability of the input array
       wSumId <- genIdent' "ws"
       declare SProb wSumId
       let wSumE = CVar wSumId
       assign wSumId (logE (intE 0))

       -- Accumulator for the max value in the input array
       wMaxId <- genIdent' "max"
       declare SProb wMaxId
       let wMaxE = CVar wMaxId
       assign wMaxId (logE (floatE 0))

       let currE = index (arrayData arrE) itE

       seqDo $ do
         -- Calculate the maximum value of the input array
         -- And calculate the total weight
         forCG (itE .=. (intE 0))
               (itE .<. (arraySize arrE))
               (CUnary CPostIncOp itE) $ do
           ifCG (wMaxE .<. currE)
                (putExprStat $ wMaxE .=. currE)
                (return ())
           logSumExpCG (S.fromList [wSumE, currE]) wSumE
         putExprStat $ wSumE .=. (wSumE .-. wMaxE)

         -- draw number from uniform(0, weightSum)
         rId <- genIdent' "r"
         declare SReal rId
         let r    = castTo [CDouble] randE
             rMax = castTo [CDouble] (CVar . Ident $ "RAND_MAX")
             rE = CVar rId
         assign rId (logE (r ./. rMax) .+. wSumE)

         assign wSumId (logE (intE 0))
         assign itId (intE 0)
         whileCG (intE 1) $
           do ifCG (rE .<. wSumE)
                   (do putExprStat $ mdataWeight loc .=. (intE 0)
                       putExprStat $ mdataSample loc .=. (itE .-. (intE 1))
                       putStat CBreak)
                   (return ())
              logSumExpCG (S.fromList [wSumE, currE .-. wMaxE]) wSumE
              putExprStat $ CUnary CPostIncOp itE


flattenMeasureOp x = error $ "TODO: flattenMeasureOp: " ++ show x

---------------
-- Superpose --
---------------

flattenSuperpose
    :: (ABT Term abt)
    => NE.NonEmpty (abt '[] 'HProb, abt '[] ('HMeasure a))
    -> (CExpr -> CodeGen ())

-- do we need to normalize?
flattenSuperpose pairs =
  let pairs' = NE.toList pairs in

  if length pairs' == 1
  then \loc -> let (w,m) = head pairs' in
         do mE <- flattenWithName m
            wE <- flattenWithName w
            putExprStat $ mdataWeight loc .=. ((mdataWeight mE) .+. wE)
            putExprStat $ mdataSample loc .=. (mdataSample mE)

  else \loc ->
         do wEs <- mapM (\(w,_) -> flattenWithName' w "w") pairs'

            wSumId <- genIdent' "ws"
            declare SProb wSumId
            let wSumE = CVar wSumId
            logSumExpCG (S.fromList wEs) wSumE

            -- draw number from uniform(0, weightSum)
            rId <- genIdent' "r"
            declare SReal rId
            let r    = castTo [CDouble] randE
                rMax = castTo [CDouble] (CVar . Ident $ "RAND_MAX")
                rE = CVar rId
            assign rId ((r ./. rMax) .*. (expE wSumE))

            -- an iterator for picking a measure
            itId <- genIdent' "it"
            declare SProb itId
            let itE = CVar itId
            assign itId (logE (intE 0))

            -- an output measure to assign to
            outId <- genIdent' "out"
            declare (typeOf . snd . head $ pairs') outId
            let outE = CVar outId

            outLabel <- genIdent' "exit"

            forM_ (zip wEs pairs')
              $ \(wE,(_,m)) ->
                  do logSumExpCG (S.fromList [itE,wE]) itE
                     ifCG (rE .<. (expE itE))
                          (flattenABT m outE >> putStat (CGoto outLabel))
                          (return ())

            putStat $ CLabel outLabel (CExpr Nothing)
            putExprStat $ mdataWeight loc .=. ((mdataWeight outE) .+. wSumE)
            putExprStat $ mdataSample loc .=. (mdataSample outE)

--------------------------------------------------------------------------------
--                           Specialized Arithmetic                           --
--------------------------------------------------------------------------------

--------------------------------------
-- LogSumExp for NaryOp Add [SProb] --
--------------------------------------
{-

Special for addition of probabilities we have a logSumExp. This will compute the
sum of the probabilities safely. Just adding the exp(a . prob) would make us
loose any of the safety from underflow that we got from storing prob in the log
domain

-}

-- the tree traversal is a depth first search
logSumExp :: S.Seq CExpr -> CExpr
logSumExp es = mkCompTree 0 1

  where lastIndex  = S.length es - 1

        compIndices :: Int -> Int -> CExpr -> CExpr -> CExpr
        compIndices i j = CCond ((S.index es i) .>. (S.index es j))

        mkCompTree :: Int -> Int -> CExpr
        mkCompTree i j
          | j == lastIndex = compIndices i j (logSumExp' i) (logSumExp' j)
          | otherwise      = compIndices i j
                               (mkCompTree i (succ j))
                               (mkCompTree j (succ j))

        diffExp :: Int -> Int -> CExpr
        diffExp a b = expm1E ((S.index es a) .-. (S.index es b))

        -- given the max index, produce a logSumExp expression
        logSumExp' :: Int -> CExpr
        logSumExp' 0 = S.index es 0
          .+. (log1pE $ foldr (\x acc -> diffExp x 0 .+. acc)
                            (diffExp 1 0)
                            [2..S.length es - 1]
                    .+. (intE $ fromIntegral lastIndex))
        logSumExp' i = S.index es i
          .+. (log1pE $ foldr (\x acc -> if i == x
                                       then acc
                                       else diffExp x i .+. acc)
                            (diffExp 0 i)
                            [1..S.length es - 1]
                    .+. (intE $ fromIntegral lastIndex))


-- | logSumExpCG creates global functions for every n-ary logSumExp function
-- this reduces code size
logSumExpCG :: S.Seq CExpr -> (CExpr -> CodeGen ())
logSumExpCG seqE =
  let size   = S.length $ seqE
      name   = "logSumExp" ++ (show size)
      funcId = Ident name
  in \loc -> do -- reset the names so that the function is the same for each arity
       let argIds = fmap Ident (take size cNameStream)
           decls  = fmap (typeDeclaration SProb) argIds
           vars   = fmap CVar argIds
       funCG [CDouble] funcId decls
         (putStat . CReturn . Just . logSumExp . S.fromList $ vars)
       putExprStat $ loc .=. (CCall (CVar funcId) (F.toList seqE))

-------------------------------------
-- LogSumExp for Summation of Prob --
-------------------------------------
{-
For summation of SProb we need a new logSumExp function that will find the max
of an array and then sum it in a loop
-}

lseSummateArrayCG
  :: ( ABT Term abt )
  => (abt '[ a ] b)
  -> CExpr
  -> (CExpr -> CodeGen ())
lseSummateArrayCG body arrayE =
  caseBind body $ \v body' ->
    \loc -> seqDo $ do
      (maxVId:maxIId:sumId:[]) <- mapM genIdent' ["maxV","maxI","sum"]
      itId <- createIdent v
      mapM_ (declare SProb) [maxVId,sumId]
      mapM_ (declare SNat)  [maxIId,itId]
      let (maxVE:maxIE:sumE:itE:[]) = fmap CVar [maxVId,maxIId,sumId,itId]
      forCG (itE .=. intE 0)
            (itE .<. arraySize arrayE)
            (CUnary CPostIncOp itE)
            (do tmpId <- genIdent
                declare SProb tmpId
                let tmpE = CVar tmpId
                flattenABT body' tmpE
                putExprStat $ derefIndex itE .=. tmpE
                putStat $ CIf ((maxVE .<. tmpE) .||. (itE .==. (intE 0)))
                              (seqCStat . fmap (CExpr . Just) $
                                [ maxVE .=. tmpE
                                , maxIE .=. itE ])
                              Nothing)
      putExprStat $ sumE  .=. (floatE 0) -- the sum is actually in real space
      forCG (itE .=. intE 0)
            (itE .<. arraySize arrayE)
            (CUnary CPostIncOp itE)
            (ifCG (itE .!=. maxIE)
                  (putExprStat $ sumE .+=. (expE ((derefIndex itE) .-. (maxVE))))
                  (return ()))

      putExprStat $ loc .=. (maxVE .+. (log1pE sumE))

  where derefIndex xE = index (arrayData arrayE) xE

---------------------
-- Kahan Summation --
---------------------
-- | given a body and a size compute the kahan summation. This should work on
--   both probs and reals
kahanSummationCG
  :: ( ABT Term abt )
  => (abt '[ a ] b)
  -> CExpr
  -> CExpr
  -> (CExpr -> CodeGen ())
kahanSummationCG body loE hiE =
  caseBind body $ \v body' ->
    \loc -> do
      (tId:cId:[]) <- mapM genIdent' ["t","c"]
      itId <- createIdent v
      declare SNat itId
      mapM_ (declare SProb) [tId,cId]
      let (tE:cE:itE:[]) = fmap CVar [tId,cId,itId]
      putExprStat $ tE .=. (floatE 0)
      putExprStat $ cE .=. (floatE 0)
      forCG (itE .=. loE)
            (itE .<. hiE)
            (CUnary CPostIncOp itE)
            (do (xId:yId:zId:[]) <- mapM genIdent' ["x","y","z"]
                mapM_ (declare SProb) [xId,yId,zId]
                let (xE:yE:zE:[]) = fmap CVar [xId,yId,zId]
                flattenABT body' xE
                putExprStat $ yE .=. (xE .-. cE)
                putExprStat $ zE .=. (tE .+. yE)
                whenPar $ putStat . CPPStat . ompToPP $ OMP Critical
                codeBlockCG $ do
                  putExprStat $ cE .=.  ((zE .-. tE) .-. yE)
                  putExprStat $ tE .=. zE)
      putExprStat $ loc .=. tE

--------------------------------------------------------------------------------
--                            Coercion Helpers                                --
--------------------------------------------------------------------------------

coerceToCG
  :: forall (a :: Hakaru) (b :: Hakaru)
  .  Coercion a b
  -> CExpr
  -> CodeGen CExpr
coerceToCG (CCons (Signed HRing_Int)            cs) e = nat2int e   >>= coerceToCG cs
coerceToCG (CCons (Signed HRing_Real)           cs) e = prob2real e >>= coerceToCG cs
coerceToCG (CCons (Continuous HContinuous_Prob) cs) e = nat2prob e  >>= coerceToCG cs
coerceToCG (CCons (Continuous HContinuous_Real) cs) e = int2real e  >>= coerceToCG cs
coerceToCG CNil e = return e

coerceFromCG
  :: forall (a :: Hakaru) (b :: Hakaru)
  .  Coercion a b
  -> CExpr
  -> CodeGen CExpr
coerceFromCG (CCons (Signed HRing_Int)            cs) e = int2nat e   >>= coerceFromCG cs
coerceFromCG (CCons (Signed HRing_Real)           cs) e = real2prob e >>= coerceFromCG cs
coerceFromCG (CCons (Continuous HContinuous_Prob) cs) e = prob2nat e  >>= coerceFromCG cs
coerceFromCG (CCons (Continuous HContinuous_Real) cs) e = real2int e  >>= coerceFromCG cs
coerceFromCG CNil e = return e

-- safe
nat2int,nat2prob,prob2real,int2real
  :: CExpr -> CodeGen CExpr
nat2int   x = return x
nat2prob  x = do x' <- localVar' SProb "n2p"
                 putExprStat $ x' .=. (logE x)
                 return x'
prob2real x = do x' <- localVar' SProb "p2r"
                 putExprStat $ x' .=. ((expm1E x) .+. (floatE 1))
                 return x'
int2real  x = return (castTo [CDouble] x)

-- unsafe
{- Because of the hkc representation of reals and probs as doubles, (instead of
   rationals). we will just silently truncate values for prob2nat and real2int
-}
int2nat,prob2nat,real2prob,real2int
  :: CExpr -> CodeGen CExpr
int2nat x =
  do x' <- localVar' SNat "i2n"
     ifCG (x .<. (intE 0))
          (do putExprStat $ printfE [ stringE "error: cannot coerce negative int to nat\n" ]
              putExprStat $ mkCallE "abort" [] )
          (putExprStat $ x' .=. (castTo [CUnsigned, CInt] x))
     return x'
prob2nat x = return (castTo [CUnsigned, CInt] x)
real2prob x =
  do x' <- localVar' SProb "r2p"
     ifCG (x .<. (intE 0))
          (do putExprStat $ printfE [ stringE "error: cannot coerce negative real to prob\n" ]
              putExprStat $ mkCallE "abort" [] )
          (putExprStat $ x' .=. (logE x))
     return x'
real2int x =  return (castTo [CInt] x)

--------------------------------------------------------------------------------
--                            Parallel Helpers                                --
--------------------------------------------------------------------------------
{- SIMD (single instruction multiple data) OpenMP pragmas, should be applied to
-- the inner most loop. `hasParallelTerm` checks whether a term or any of its
-- subterms contain a parallel construct { plate, summate, product, array,
-- bucket }.
-}

hasParallelTerm :: ( ABT Term abt ) => abt '[] a -> Bool
hasParallelTerm abt = caseVarSyn abt (const False) hPT'
  where hPT' :: ABT Term abt => Term abt a -> Bool
        hPT' (_ :$ _)          = undefined
        hPT' (NaryOp_ _ _)     = undefined
        hPT' (Literal_ _)      = False
        hPT' (Empty_ _)        = False
        hPT' (Array_ _ _)      = True
        hPT' (ArrayLiteral_ _) = False
        hPT' (Bucket _ _ _)    = True
        hPT' (Datum_ _)        = False
        hPT' (Case_ _ _)       = undefined
        hPT' (Superpose_ _)    = undefined
        hPT' (Reject_ _)       = False

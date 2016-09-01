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
  ( flattenABT )
  where

import Language.Hakaru.CodeGen.CodeGenMonad
import Language.Hakaru.CodeGen.HOAS.Declaration
import Language.Hakaru.CodeGen.HOAS.Expression
import Language.Hakaru.CodeGen.HOAS.Statement

import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.TypeOf (typeOf)
import Language.Hakaru.Syntax.Datum
import Language.Hakaru.Syntax.IClasses
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Types.HClasses
import Language.Hakaru.Types.Coercion
import Language.Hakaru.Types.Sing

import Language.C.Syntax.AST
import Language.C.Data.Ident

import           Control.Monad.State.Strict
import           Data.Number.Natural
import           Data.Ratio
import qualified Data.List.NonEmpty as NE
import qualified Data.Sequence      as S
import qualified Data.Foldable      as F
import qualified Data.Traversable   as T


#if __GLASGOW_HASKELL__ < 710
import           Data.Functor
#endif


import Prelude hiding (log,exp,sqrt)

flattenABT :: ABT Term abt
           => abt '[] a
           -> CodeGen CExpr
flattenABT abt = caseVarSyn abt flattenVar flattenTerm

flattenLambda
  :: ABT Term abt
  => abt '[] a
  -> Ident
  -> CodeGen ()
flattenLambda abt name =
    coalesceLambda abt $ \vars abt' ->
    let varMs = foldMap11 (\v -> [mkVarDecl v =<< createIdent v]) vars
    in  do argDecls <- sequence varMs

           cg <- get
           let m       = putStat . returnS =<< flattenABT abt'
               (_,cg') = runState m $ cg { statements = []
                                         , declarations = [] }
           put $ cg' { statements   = statements cg
                     , declarations = declarations cg }

           extDeclare . extFunc $ functionDef (typeOf abt')
                                              name
                                              argDecls
                                              (reverse $ declarations cg')
                                              (reverse $ statements cg')
  -- do at top level
  where coalesceLambda
          :: ABT Term abt
          => abt '[] a
          -> ( forall (ys :: [Hakaru]) b
             . List1 Variable ys -> abt '[] b -> r)
          -> r
        coalesceLambda abt k =
          caseVarSyn abt (const (k Nil1 abt)) $ \term ->
            case term of
              (Lam_ :$ body :* End) ->
                caseBind body $ \v body' ->
                  coalesceLambda body' $ \vars body'' -> k (Cons1 v vars) body''
              _ -> k Nil1 abt
            

        mkVarDecl :: Variable (a :: Hakaru) -> Ident -> CodeGen CDecl
        mkVarDecl (Variable _ _ SInt)  = return . typeDeclaration SInt
        mkVarDecl (Variable _ _ SNat)  = return . typeDeclaration SNat
        mkVarDecl (Variable _ _ SProb) = return . typeDeclaration SProb
        mkVarDecl (Variable _ _ SReal) = return . typeDeclaration SReal
        mkVarDecl (Variable _ _ (SArray t)) = \i -> do extDeclare $ arrayStruct t
                                                       return $ arrayDeclaration t i
        mkVarDecl (Variable _ _ d@(SData _ _)) = \i -> do extDeclare $ datumStruct d
                                                          return $ datumDeclaration d i
        mkVarDecl v = error $ "flattenSCon.Lam_.mkVarDecl cannot handle vars of type " ++ show v
                      

flattenVar :: Variable (a :: Hakaru) -> CodeGen CExpr
flattenVar v = varE <$> lookupIdent v

flattenTerm :: ABT Term abt => Term abt a -> CodeGen CExpr
flattenTerm (NaryOp_ t s)    = flattenNAryOp t s
flattenTerm (Literal_ x)     = flattenLit x
flattenTerm (Empty_ _)       = error "TODO: flattenTerm Empty"
flattenTerm (Datum_ d)       = flattenDatum d
flattenTerm (Case_ c bs)     = flattenCase c bs
flattenTerm (Array_ s e)     = flattenArray s e
flattenTerm (x :$ ys)        = flattenSCon x ys
flattenTerm (Reject_ _)      = error "TODO: flattenTerm Reject"
flattenTerm (Superpose_ wes) = flattenSuperpose wes

----------------------------------------------------------------


flattenSCon :: ( ABT Term abt )
            => SCon args a
            -> SArgs abt args
            -> CodeGen CExpr
flattenSCon Let_            =
  \(expr :* body :* End) ->
    do expr' <- flattenABT expr
       caseBind body $ \v@(Variable _ _ typ) body'->
         do ident <- createIdent v
            declare typ ident
            assign ident expr'
            flattenABT body'

-- Lambdas produce functions and then return a function pointer
flattenSCon Lam_            =
  \(body :* End) ->
    coalesceLambda body $ \vars body' ->
    let varMs = foldMap11 (\v -> [mkVarDecl v =<< createIdent v]) vars
    in  do funcId <- genIdent' "fn"
           argDecls <- sequence varMs

           cg <- get
           let m       = putStat . returnS =<< flattenABT body'
               (_,cg') = runState m $ cg { statements = []
                                         , declarations = [] }
           put $ cg' { statements   = statements cg
                     , declarations = declarations cg }

           extDeclare . extFunc $ functionDef (typeOf body')
                                              funcId
                                              argDecls
                                              (reverse $ declarations cg')
                                              (reverse $ statements cg')
           return . varE $ funcId
  -- do at top level
  where coalesceLambda
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

        mkVarDecl :: Variable (a :: Hakaru) -> Ident -> CodeGen CDecl
        mkVarDecl (Variable _ _ SInt)  = return . typeDeclaration SInt
        mkVarDecl (Variable _ _ SNat)  = return . typeDeclaration SNat
        mkVarDecl (Variable _ _ SProb) = return . typeDeclaration SProb
        mkVarDecl (Variable _ _ SReal) = return . typeDeclaration SReal
        mkVarDecl (Variable _ _ (SArray t)) = \i -> do extDeclare $ arrayStruct t
                                                       return $ arrayDeclaration t i
        mkVarDecl (Variable _ _ d@(SData _ _)) = \i -> do extDeclare $ datumStruct d
                                                          return $ datumDeclaration d i
        mkVarDecl v = error $ "flattenSCon.Lam_.mkVarDecl cannot handle vars of type " ++ show v


flattenSCon (PrimOp_ op)    = flattenPrimOp op
flattenSCon (ArrayOp_ op)   = flattenArrayOp op
flattenSCon (MeasureOp_ op) = flattenMeasureOp op
flattenSCon Dirac           = \(e :* End) -> flattenABT e

flattenSCon (Summate _ sr) = \(lo :* hi :* body :* End) ->
  do loE <- flattenABT lo
     hiE <- flattenABT hi
     caseBind body $ \v body' ->
       do iterI <- createIdent v
          declare SNat iterI
          assign iterI loE

          accI <- genIdent' "acc"
          declare (sing_HSemiring sr) accI
          assign accI (intConstE 0)

          let accVar  = varE accI
              iterVar = varE iterI
          -- logSumExp for probabilities
          forCG iterVar (iterVar ^< hiE) (postInc iterVar) $
            do bodyE <- flattenABT body'
               assign accI (accVar ^+ bodyE)

          return accVar


flattenSCon (Product _ sr) = \(lo :* hi :* body :* End) ->
  do loE <- flattenABT lo
     hiE <- flattenABT hi
     caseBind body $ \v body' ->
       do iterI <- createIdent v
          declare SNat iterI
          assign iterI loE

          accI <- genIdent' "acc"
          declare (sing_HSemiring sr) accI
          assign accI (intConstE 1)

          let accVar  = varE accI
              iterVar = varE iterI
          forCG iterVar (iterVar ^< hiE) (postInc iterVar) $
            do bodyE <- flattenABT body'
               assign accI (accVar ^* bodyE)

          return accVar


flattenSCon MBind           =
  \(e1 :* e2 :* End) ->
    do e1' <- flattenABT e1
       caseBind e2 $ \v@(Variable _ _ typ) e2'->
         do ident <- createIdent v
            declare typ ident
            assign ident e1'
            flattenABT e2'

-- at this point, only nonrecusive coersions are implemented
flattenSCon (CoerceTo_ (CCons t CNil)) =
  \(e :* End) ->
    do e' <- flattenABT e
       coerceToType t (typeOf e) e' 
  where coerceToType
          :: PrimCoercion b c
          -> Sing (a :: Hakaru)
          -> CExpr
          -> CodeGen CExpr
        coerceToType (Signed HRing_Int)  SNat  = nat2int
        coerceToType (Signed HRing_Real) SProb = prob2real
        coerceToType (Continuous HContinuous_Prob) SNat = nat2prob
        coerceToType (Continuous HContinuous_Real) SInt = int2real
        coerceToType t1 t2 = error $ "TODO? coerceToType: " ++ show t1 ++ " to " ++ show t2

        -- implementing ONLY functions found in Hakaru.Syntax.AST
        nat2int,nat2prob,prob2real,int2real
          :: CExpr -> CodeGen CExpr
        nat2int   = return
        nat2prob  = \n -> do ident <- genIdent' "p"
                             declare SProb ident
                             assign ident . log1p $ n ^- (intConstE 1)
                             return (varE ident)
        prob2real = \p -> do ident <- genIdent' "r"
                             declare SReal ident
                             assign ident $ (expm1 p) ^+ (intConstE 1)
                             return (varE ident)
        int2real  = return . castE doubleDecl

flattenSCon x               = \_ -> error $ "TODO: flattenSCon: " ++ show x


----------------------------------------------------------------
flattenNAryOp :: ABT Term abt
              => NaryOp a
              -> S.Seq (abt '[] a)
              -> CodeGen CExpr
flattenNAryOp op args =
  do es <- T.mapM flattenABT args
     case op of
       (Sum HSemiring_Prob)  ->
         do ident <- genIdent' "logSumExp"
            declare SProb ident
            assign ident $ logSumExp es
            return (varE ident)

       -- otherwise
       _ -> return $ F.foldr (binaryOp op)
                             (S.index es 0)
                             (S.drop 1 es)

-- logSumExp codegen involves producing a tree of comparisons, where
-- the leaves are logSumExp expressions
--
-- the tree traversal is a depth first search
logSumExp :: S.Seq CExpr -> CExpr
logSumExp es = mkCompTree 0 1

  where lastIndex  = S.length es - 1

        compIndices :: Int -> Int -> CExpr -> CExpr -> CExpr
        compIndices i j = condE ((S.index es i) ^> (S.index es j))

        mkCompTree :: Int -> Int -> CExpr
        mkCompTree i j
          | j == lastIndex = compIndices i j (logSumExp' i) (logSumExp' j)
          | otherwise      = compIndices i j
                               (mkCompTree i (succ j))
                               (mkCompTree j (succ j))

        diffExp :: Int -> Int -> CExpr
        diffExp a b = expm1 ((S.index es a) ^- (S.index es b))

        -- given the max index, produce a logSumExp expression
        logSumExp' :: Int -> CExpr
        logSumExp' 0 = S.index es 0
          ^+ (log1p $ foldr (\x acc -> diffExp x 0 ^+ acc)
                            (diffExp 1 0)
                            [2..S.length es - 1]
                    ^+ (intConstE $ fromIntegral lastIndex))
        logSumExp' i = S.index es i
          ^+ (log1p $ foldr (\x acc -> if i == x
                                       then acc
                                       else diffExp x i ^+ acc)
                            (diffExp 0 i)
                            [1..S.length es - 1]
                    ^+ (intConstE $ fromIntegral lastIndex))



----------------------------------------------------------------


flattenLit :: Literal a -> CodeGen CExpr
flattenLit lit =
  case lit of
    (LNat x)  -> return (intConstE $ fromIntegral x)
    (LInt x)  -> return (intConstE x)
    (LReal x) -> return (floatConstE $ fromRational x)
    (LProb x) -> let rat = fromNonNegativeRational x
                     x'  = (fromIntegral $ numerator rat)
                         / (fromIntegral $ denominator rat)
                 in do pId <- genIdent' "p"
                       declare SProb pId
                       assign pId $ log1p (floatConstE x' ^- intConstE 1)
                       return (varE pId)

----------------------------------------------------------------


flattenArray :: (ABT Term abt)
             => (abt '[] 'HNat)
             -> (abt '[ 'HNat ] a)
             -> CodeGen CExpr
flattenArray arity body =
  caseBind body $ \v body' ->
    do let arrTyp = typeOf body'
       arrayIdent <- genIdent' "arr"
       declare (SArray arrTyp) arrayIdent

       arity'     <- flattenABT arity

       let arrVar  = varE arrayIdent
           dataPtr = arrVar ^! (builtinIdent "data")
           sizeVar = arrVar ^! (builtinIdent "size")
           dataTyp = buildType arrTyp -- this should be a literal type (unless we can have an array of measures)
       putStat $ assignExprS sizeVar arity'

       -- setup loop
       putStat $ assignExprS dataPtr $ castE (mkPtrDecl dataTyp)
                                             (malloc (arity' ^* (sizeof . mkDecl $ dataTyp)))

       iterIdent  <- createIdent v
       declare SNat iterIdent
       assign iterIdent (intConstE 0)

       -- manage loop
       let iter     = varE iterIdent
           cond     = iter ^< arity'
           inc      = postInc iter
           currInd  = indirectE (dataPtr ^+ iter)
           loopBody = putStat . assignExprS currInd =<< flattenABT body'
       forCG iter cond inc loopBody

       return (varE arrayIdent)

----------------------------------------------------------------

flattenArrayOp
  :: ( ABT Term abt
     -- , typs ~ UnLCs args
     , args ~ LCs typs
     )
  => ArrayOp typs a
  -> SArgs abt args
  -> CodeGen CExpr
flattenArrayOp (Index _)  = \(e1 :* e2 :* End) ->
  do arr <- flattenABT e1
     ind <- flattenABT e2
     let dataPtr = arr ^! (builtinIdent "data")
     return . indirectE $ (dataPtr ^+ ind)
flattenArrayOp (Size _)   = \(e1 :* End) ->
  do arr <- flattenABT e1
     return (arr ^! (builtinIdent "size"))
flattenArrayOp (Reduce _) = \(fun :* base :* arr :* End) ->
  do funE  <- flattenABT fun
     baseE <- flattenABT base
     arrE  <- flattenABT arr
     accI  <- genIdent' "acc"
     iterI <- genIdent' "iter"

     let sizeE = arrE ^! (builtinIdent "size")
         iterE = varE iterI
         accE  = varE accI
         cond  = iterE ^< sizeE
         inc   = postInc iterE

     declare (typeOf base) accI
     declare SInt iterI
     assign accI baseE
     forCG iterE cond inc $
       assign accI $ callFuncE funE [accE]

     return accE

----------------------------------------------------------------



flattenDatum
  :: (ABT Term abt)
  => Datum (abt '[]) (HData' a)
  -> CodeGen CExpr
flattenDatum (Datum _ typ code) =
  do ident <- genIdent
     extDeclare $ datumStruct typ
     declare typ ident
     assignDatum code ident
     return (varE ident)

datumNames :: [String]
datumNames = filter (\n -> not $ elem (head n) ['0'..'9']) names
  where base = ['0'..'9'] ++ ['a'..'z']
        names = [[x] | x <- base] `mplus` (do n <- names
                                              [n++[x] | x <- base])

assignDatum
  :: (ABT Term abt)
  => DatumCode xss (abt '[]) c
  -> Ident
  -> CodeGen ()
assignDatum code ident =
  let index     = getIndex code
      indexExpr = memberE (varE ident) (builtinIdent "index")
  in  do putStat   $ assignExprS indexExpr (intConstE index)
         sequence_ $ assignSum code ident
  where getIndex :: DatumCode xss b c -> Integer
        getIndex (Inl _)    = 0
        getIndex (Inr rest) = succ (getIndex rest)

assignSum
  :: (ABT Term abt)
  => DatumCode xs (abt '[]) c
  -> Ident
  -> [CodeGen ()]
assignSum code ident = fst $ runState (assignSum' code ident) datumNames

assignSum'
  :: (ABT Term abt)
  => DatumCode xs (abt '[]) c
  -> Ident
  -> State [String] [CodeGen ()]
assignSum' (Inr rest) topIdent =
  do (_:names) <- get
     put names
     assignSum' rest topIdent
assignSum' (Inl prod) topIdent =
  do (name:_) <- get
     return $ assignProd prod topIdent (builtinIdent name)

assignProd
  :: (ABT Term abt)
  => DatumStruct xs (abt '[]) c
  -> Ident
  -> Ident
  -> [CodeGen ()]
assignProd dstruct topIdent sumIdent =
  fst $ runState (assignProd' dstruct topIdent sumIdent) datumNames

assignProd'
  :: (ABT Term abt)
  => DatumStruct xs (abt '[]) c
  -> Ident
  -> Ident
  -> State [String] [CodeGen ()]
assignProd' Done _ _ = return []
assignProd' (Et (Konst d) rest) topIdent sumIdent =
  do (name:names) <- get
     put names
     let varName  = memberE (memberE (memberE (varE topIdent)
                                              (builtinIdent "sum"))
                                     sumIdent)
                            (internalIdent name)
         assignCG = putStat =<< assignExprS varName <$> flattenABT d
     rest' <- assignProd' rest topIdent sumIdent
     return $ [assignCG] ++ rest'
assignProd' _ _ _  = error $ "TODO: assignProd Ident"


----------------------------------------------------------------

flattenCase
  :: forall abt a b
  .  (ABT Term abt)
  => abt '[] a
  -> [Branch a abt b]
  -> CodeGen CExpr
flattenCase c (Branch (PDatum _ (PInl PDone)) trueB:Branch (PDatum _ (PInr (PInl PDone))) falseB:[]) =
  do c' <- flattenABT c
     result <- genIdent
     declare (typeOf trueB) result
     cg <- get
     let trueM    = assign result =<< flattenABT trueB
         falseM   = assign result =<< flattenABT falseB
         (_,cg')  = runState trueM $ cg { statements = [] }
         (_,cg'') = runState falseM $ cg' { statements = [] }
     put $ cg'' { statements = statements cg }

     putStat $ compoundGuardS ((c' ^! (builtinIdent "index")) ^== (intConstE 0)) (reverse $ statements cg')
     putStat $ compoundGuardS ((c' ^! (builtinIdent "index")) ^== (intConstE 1)) (reverse $ statements cg'')
     return (varE result)
flattenCase _ _ = error "TODO: flattenCase"


----------------------------------------------------------------


flattenPrimOp :: ( ABT Term abt
                 , typs ~ UnLCs args
                 , args ~ LCs typs)
              => PrimOp typs a
              -> SArgs abt args
              -> CodeGen CExpr
flattenPrimOp Pi = \End ->
  do ident <- genIdent
     declare SProb ident
     assign ident $ log1p ((stringVarE "M_PI") ^- (intConstE 1))
     return (varE ident)
flattenPrimOp (Recip t) =
  \(a :* End) ->
    do aE <- flattenABT a
       recipIdent <- genIdent
       let recipV = varE recipIdent
       case t of
         HFractional_Real ->
           do declare SReal recipIdent
              assign recipIdent ((intConstE 1) ^/ aE)
              return recipV
         HFractional_Prob ->
           do declare SProb recipIdent
              assign recipIdent (log1p (((intConstE 1) ^/ (expm1 (aE ^+ (intConstE 1)))) ^- (intConstE 1)))
              return recipV
         
flattenPrimOp (Equal _) = \(a :* b :* End) ->
  do a' <- flattenABT a
     b' <- flattenABT b
     -- special case for booleans
     let a'' = case typeOf a of
                 (SData _ (SPlus SDone (SPlus SDone SVoid))) -> (a' ^! (builtinIdent "index"))
                 _ -> a'
         b'' = case typeOf a of
                 (SData _ (SPlus SDone (SPlus SDone SVoid))) -> (b' ^! (builtinIdent "index"))
                 _ -> b'
     boolIdent <- genIdent' "eq"

     declare sBool boolIdent
     putStat $ assignExprS ((varE boolIdent) ^! (builtinIdent "index"))
                           (condE (a'' ^== b'') (intConstE 0) (intConstE 1))

     return (varE boolIdent)

  
flattenPrimOp (Less _) = \(a :* b :* End) ->
  do a' <- flattenABT a
     b' <- flattenABT b
     boolIdent <- genIdent' "less"

     declare sBool boolIdent
     putStat $ assignExprS ((varE boolIdent) ^! (builtinIdent "index"))
                           (condE (a' ^< b') (intConstE 0) (intConstE 1))

     return (varE boolIdent)
  
flattenPrimOp t  = \_ -> error $ "TODO: flattenPrimOp: " ++ show t

----------------------------------------------------------------


flattenMeasureOp :: ( ABT Term abt
                    , typs ~ UnLCs args
                    , args ~ LCs typs)
                 => MeasureOp typs a
                 -> SArgs abt args
                 -> CodeGen CExpr
flattenMeasureOp Normal  = \(a :* b :* End) ->
  let randomE = (castE doubleDecl rand)
              ^/ (castE doubleDecl (stringVarE "RAND_MAX")) in
  do a' <- flattenABT a
     b' <- flattenABT b

     uId <- genIdent
     declare SReal uId
     let varU = varE uId

     vId <- genIdent
     declare SReal vId
     let varV = varE vId

     rId <- genIdent
     let varR = varE rId
     declare SReal rId


     doWhileCG ((varR ^== (intConstE 0)) ^|| (varR ^> (intConstE 1)))
       $ do assign uId $ randomE ^* (floatConstE 2) ^- (floatConstE 1)
            assign vId $ randomE ^* (floatConstE 2) ^- (floatConstE 1)
            assign rId $ (varU ^* varU) ^+ (varV ^* varV)

     cId <- genIdent
     declare SReal cId
     assign cId $ sqrt ((unaryE "-" (intConstE 2)) ^* (log varR ^/ varR))
     let varC = varE cId

     return (a' ^+ (varU ^* (varC ^* b')))

flattenMeasureOp Uniform = \(a :* b :* End) ->
  do a' <- flattenABT a
     b' <- flattenABT b
     ident <- genIdent
     declare SReal ident
     let r    = castE doubleDecl rand
         rMax = castE doubleDecl (stringVarE "RAND_MAX")
     assign ident (a' ^+ ((r ^/ rMax) ^* (b' ^- a')))
     return (varE ident)
flattenMeasureOp x = error $ "TODO: flattenMeasureOp: " ++ show x

----------------------------------------------------------------

flattenSuperpose
    :: (ABT Term abt)
    => NE.NonEmpty (abt '[] 'HProb, abt '[] ('HMeasure a))
    -> CodeGen CExpr

-- do we need to normalize?
flattenSuperpose wes =
  let wes' = NE.toList wes in
  do randId <- genIdent' "rand"
     declare SReal randId
     let r    = castE doubleDecl rand
         rMax = castE doubleDecl (stringVarE "RAND_MAX")
         rVar = varE randId
     assign randId ((r ^/ rMax) ^* (intConstE 1))


     outId <- genIdent
     declare SReal outId

     wes'' <- T.forM  wes'  $ \(p,m) -> do p' <- flattenABT p
                                           m' <- flattenABT m
                                           return ((exp p') ^< rVar, assignS outId m')

     putStat (listOfIfsS wes'')

     return (varE outId)

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
  , flattenTerm )
  where

import Language.Hakaru.CodeGen.CodeGenMonad
import Language.Hakaru.CodeGen.AST
import Language.Hakaru.CodeGen.Types

import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.TypeOf (typeOf)
import Language.Hakaru.Syntax.Datum hiding (Ident)
import Language.Hakaru.Syntax.IClasses
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Types.HClasses
import Language.Hakaru.Types.Coercion
import Language.Hakaru.Types.Sing

import           Control.Monad.State.Strict
import           Control.Monad (replicateM)
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

flattenVar :: Variable (a :: Hakaru) -> CodeGen CExpr
flattenVar v = CVar <$> lookupIdent v

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
           let m       = putStat . CReturn . Just =<< flattenABT body'
               (_,cg') = runState m $ cg { statements = []
                                         , declarations = [] }
           put $ cg' { statements   = statements cg
                     , declarations = declarations cg }

           extDeclare . CFunDefExt $ functionDef (typeOf body')
                                                 funcId
                                                 argDecls
                                                 (reverse $ declarations cg')
                                                 (reverse $ statements cg')
           return . CVar $ funcId
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
flattenSCon Dirac           = \(e :* End) ->
  do e' <- flattenABT e
     (Sample sampleId _) <- getSample
     putSample (Sample sampleId e')
     return (intE 0)


flattenSCon Plate           = \(size :* b :* End) ->
  caseBind b $ \v body ->
    do arity <- flattenABT size
       iterIdent  <- createIdent v
       declare SNat iterIdent

       (Sample i _) <- getSample

       -- manage loop
       let iter     = CVar iterIdent
           cond     = iter .<. arity
           inc      = CUnary CPostIncOp iter
           currInd  = indirect ((CMember (CVar i) (Ident "data") False) .+. iter)
           loopBody = do _ <- flattenABT body
                         (Sample _ e) <- getSample
                         putStat . CExpr . Just $ currInd .=. e
       forCG (iter .=. (intE 0)) cond inc loopBody
       return (intE 0)


flattenSCon (Summate _ sr) = \(lo :* hi :* body :* End) ->
  do loE <- flattenABT lo
     hiE <- flattenABT hi
     caseBind body $ \v body' ->
       do iterI <- createIdent v
          declare SNat iterI

          accI <- genIdent' "acc"
          declare (sing_HSemiring sr) accI
          assign accI (intE 0)

          let accVar  = CVar accI
              iterVar = CVar iterI
          -- logSumExp for probabilities
          reductionCG CAddOp
                      accI
                      (iterVar .=. loE)
                      (iterVar .<. hiE)
                      (CUnary CPostIncOp iterVar) $
            do bodyE <- flattenABT body'
               putStat . CExpr . Just $ (accVar .+=. bodyE)

          return accVar


flattenSCon (Product _ sr) = \(lo :* hi :* body :* End) ->
  do loE <- flattenABT lo
     hiE <- flattenABT hi
     caseBind body $ \v body' ->
       do iterI <- createIdent v
          declare SNat iterI

          accI <- genIdent' "acc"
          declare (sing_HSemiring sr) accI
          assign accI (intE 1)

          let accVar  = CVar accI
              iterVar = CVar iterI
          reductionCG (case sing_HSemiring sr of
                         SProb -> CAddOp
                         _     -> CMulOp)
                      accI
                      (iterVar .=. loE)
                      (iterVar .<. hiE)
                      (CUnary CPostIncOp iterVar) $
            do bodyE <- flattenABT body'
               putStat . CExpr . Just . (case sing_HSemiring sr of
                                           SProb -> CAssign CAddAssOp accVar
                                           _     -> CAssign CMulAssOp accVar)
                 $ bodyE

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
flattenSCon (CoerceTo_ ctyp) =
  \(e :* End) -> flattenABT e >>= coerceToType ctyp (typeOf e)
  where coerceToType
          :: Coercion a b
          -> Sing (c :: Hakaru)
          -> CExpr
          -> CodeGen CExpr
        coerceToType (CCons p rest) typ =
          \e ->  primitiveCoerce p typ e >>= coerceToType rest typ
        coerceToType CNil            _  = return . id

        primitiveCoerce
          :: PrimCoercion a b
          -> Sing (c :: Hakaru)
          -> CExpr
          -> CodeGen CExpr
        primitiveCoerce (Signed HRing_Int)            SNat  = nat2int
        primitiveCoerce (Signed HRing_Real)           SProb = prob2real
        primitiveCoerce (Continuous HContinuous_Prob) SNat  = nat2prob
        primitiveCoerce (Continuous HContinuous_Real) SInt  = int2real
        primitiveCoerce (Continuous HContinuous_Real) SNat  = int2real
        primitiveCoerce a b = error $ "flattenSCon CoerceTo_: cannot preform coersion "
                                    ++ show a
                                    ++ " to "
                                    ++ show b


        -- implementing ONLY functions found in Hakaru.Syntax.AST
        nat2int,nat2prob,prob2real,int2real
          :: CExpr -> CodeGen CExpr
        nat2int   = return
        nat2prob  = \n -> do ident <- genIdent' "p"
                             declare SProb ident
                             assign ident . log1p $ n .-. (intE 1)
                             return (CVar ident)
        prob2real = \p -> do ident <- genIdent' "r"
                             declare SReal ident
                             assign ident $ (expm1 p) .+. (intE 1)
                             return (CVar ident)
        int2real  = return . CCast doubleDecl

flattenSCon x               = \_ -> error $ "TODO: flattenSCon: " ++ show x


----------------------------------------------------------------
flattenNAryOp :: ABT Term abt
              => NaryOp a
              -> S.Seq (abt '[] a)
              -> CodeGen CExpr
flattenNAryOp op args =
  do es <- T.mapM flattenABT args
     case op of
       And -> boolNaryOp op "and" es
       Or  -> boolNaryOp op "or"  es
       Xor -> boolNaryOp op "xor" es
       Iff -> boolNaryOp op "iff" es

       (Sum HSemiring_Prob)  ->
         do ident <- genIdent' "logSumExp"
            declare SProb ident
            assign ident =<< logSumExpCG es
            return (CVar ident)

       -- otherwise
       _ -> return $ F.foldr (binaryOp op)
                             (S.index es 0)
                             (S.drop 1 es)
  where boolNaryOp op' str es' =
          do ident <- genIdent' str
             declare sBool ident
             let indexOf x = CMember x (Ident "index") True
                 es''      = fmap indexOf es'
                 v         = CVar ident
                 expr      = F.foldr (binaryOp op')
                                     (S.index es'' 0)
                                     (S.drop 1 es'')
             putStat . CExpr . Just $ (indexOf v) .=. expr
             return v


-- logSumExp codegen involves producing a tree of comparisons, where
-- the leaves are logSumExp expressions
--
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
        diffExp a b = expm1 ((S.index es a) .-. (S.index es b))

        -- given the max index, produce a logSumExp expression
        logSumExp' :: Int -> CExpr
        logSumExp' 0 = S.index es 0
          .+. (log1p $ foldr (\x acc -> diffExp x 0 .+. acc)
                            (diffExp 1 0)
                            [2..S.length es - 1]
                    .+. (intE $ fromIntegral lastIndex))
        logSumExp' i = S.index es i
          .+. (log1p $ foldr (\x acc -> if i == x
                                       then acc
                                       else diffExp x i .+. acc)
                            (diffExp 0 i)
                            [1..S.length es - 1]
                    .+. (intE $ fromIntegral lastIndex))


-- | logSumExpCG creates a functions for every n-ary logSumExp function
-- this function shouldn't be used until CodeGen has a partial ordering on ExtDecls
logSumExpCG :: S.Seq CExpr -> CodeGen CExpr
logSumExpCG seqE =
  let size   = S.length $ seqE
      name   = "logSumExp" ++ (show size)
      funcId = Ident name
  in  do -- reset the names so that the function is the same for each arity
         cg <- get
         put (cg { freshNames = suffixes })
         argIds <- replicateM size genIdent
         let decls = fmap (typeDeclaration SProb) argIds
             vars  = fmap CVar argIds
         extDeclare . CFunDefExt $ functionDef SProb
                                               funcId
                                               decls
                                               []
                                               [CReturn . Just $ logSumExp $ S.fromList vars ]
         cg' <- get
         put (cg' { freshNames = freshNames cg })
         return $ CCall (CVar funcId) (F.toList seqE)



----------------------------------------------------------------


flattenLit :: Literal a -> CodeGen CExpr
flattenLit lit =
  case lit of
    (LNat x)  -> return (intE $ fromIntegral x)
    (LInt x)  -> return (intE x)
    (LReal x) -> return (floatE $ fromRational x)
    (LProb x) -> let rat = fromNonNegativeRational x
                     x'  = (fromIntegral $ numerator rat)
                         / (fromIntegral $ denominator rat)
                 in do pId <- genIdent' "p"
                       declare SProb pId
                       assign pId $ log1p (floatE x' .-. intE 1)
                       return (CVar pId)

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

       let arrVar  = CVar arrayIdent
           dataPtr = CMember arrVar (Ident "data") True
           sizeVar = CMember arrVar (Ident "size") True
           dataTyp = case buildType arrTyp of
                       [] -> error "flatten: this shouldn't happen"
                       t  -> t
           -- this should be a literal type (unless we can have an array of measures)
       putStat . CExpr . Just $ sizeVar .=. arity'

       -- setup loop
       putStat . CExpr . Just $ dataPtr .=. (CCast (mkPtrDecl dataTyp)
                                                   (mkUnary "malloc"
                                                            (arity' .*. (CSizeOfType . mkDecl $ dataTyp))))

       iterIdent  <- createIdent v
       declare SNat iterIdent

       -- manage loop
       let iter     = CVar iterIdent
           cond     = iter .<. arity'
           inc      = CUnary CPostIncOp iter
           currInd  = indirect (dataPtr .+. iter)
           loopBody = putStat . CExpr . Just . CAssign CAssignOp currInd =<< flattenABT body'
       -- mpB <- isOpenMP
       -- when mpB . putStat . CPPStat . PPPragma
       --      $ ["omp","parallel","for"]
       forCG (iter .=. (intE 0)) cond inc loopBody

       return (CVar arrayIdent)

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
     let dataPtr = CMember arr (Ident "data") True
     return . indirect $ (dataPtr .+. ind)
flattenArrayOp (Size _)   = \(e1 :* End) ->
  do arr <- flattenABT e1
     return (CMember arr (Ident "size") True)
flattenArrayOp (Reduce _) = \(fun :* base :* arr :* End) ->
  do funE  <- flattenABT fun
     baseE <- flattenABT base
     arrE  <- flattenABT arr
     accI  <- genIdent' "acc"
     iterI <- genIdent' "iter"

     let sizeE = CMember arrE (Ident "size") True
         iterE = CVar iterI
         accE  = CVar accI
         cond  = iterE .<. sizeE
         inc   = CUnary CPostIncOp iterE

     declare (typeOf base) accI
     declare SInt iterI
     assign accI baseE
     forCG (iterE .=. (intE 0)) cond inc $
       assign accI $ CCall funE [accE]

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
     return (CVar ident)

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
      indexExpr = CMember (CVar ident) (Ident "index") True
  in  do putStat . CExpr . Just $ indexExpr .=. (intE index)
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
     return $ assignProd prod topIdent (Ident name)

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
     let varName  = CMember (CMember (CMember (CVar topIdent)
                                              (Ident "sum")
                                              True)
                                     sumIdent
                                     True)
                            (Ident name)
                            True
         assignCG = putStat . CExpr . Just =<< CAssign CAssignOp varName <$> flattenABT d
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

     putStat $ CIf ((CMember c' (Ident "index") True) .==. (intE 0))
                   (CCompound . fmap CBlockStat . reverse . statements $ cg')
                   Nothing
     putStat $ CIf ((CMember c' (Ident "index") True) .==. (intE 1))
                   (CCompound . fmap CBlockStat . reverse . statements $ cg'')
                   Nothing
     return (CVar result)
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
     assign ident $ log1p ((CVar . Ident $ "M_PI") .-. (intE 1))
     return (CVar ident)

flattenPrimOp RealPow =
  \(a :* b :* End) ->
  do ident <- genIdent' "pow"
     declare SReal ident
     aE <- flattenABT a -- first argument is a Prob
     bE <- flattenABT b
     let realPow = CCall (CVar . Ident $ "pow") [ expm1 aE .+. (intE 1), bE]
     assign ident $ log1p (realPow .-. (intE 1))
     return $ CVar ident

-- flattenPrimOp (NatPow baseT) =
--   \(a :* b :* End) ->
--   let singBase = sing_HSemiring baseT in
--   do ident <- genIdent' "pow"
--      declare singBase ident
--      aE <- flattenABT a
--      bE <- flattenABT b
--      let powerOf x y = callFuncE (varE . builtinIdent $ "pow") [x,y]
--          value = case singBase of
--                         SProb -> log1p (powerOf (expm1 aE ^+ (intConstE 1)) bE
--                                          ^- (intConstE 1))
--                         _     -> powerOf (expm1 aE ^+ (intConstE 1)) bE
--      assign ident $ value
--      return $ varE ident

-- flattenPrimOp (NatRoot _) =
--   \(a :* b :* End) ->
--   do ident <- genIdent' "root"
--      declare SProb ident
--      aE <- flattenABT a
--      bE <- flattenABT b
--      let powerOf x y = callFuncE (varE . builtinIdent $ "pow") [x,y]
--          recipBE = (intConstE 1) ^/ bE
--      assign ident $ log1p (powerOf (expm1 aE ^+ (intConstE 1)) recipBE ^- (intConstE 1))
--      return $ varE ident


flattenPrimOp (Recip t) =
  \(a :* End) ->
    do aE <- flattenABT a
       recipIdent <- genIdent
       let recipV = CVar recipIdent
       case t of
         HFractional_Real ->
           do declare SReal recipIdent
              assign recipIdent ((intE 1) ./. aE)
              return recipV
         HFractional_Prob ->
           do declare SProb recipIdent
              assign recipIdent (CUnary CMinOp aE)
              return recipV

flattenPrimOp (Equal _) = \(a :* b :* End) ->
  do a' <- flattenABT a
     b' <- flattenABT b
     -- special case for booleans
     let a'' = case typeOf a of
                 (SData _ (SPlus SDone (SPlus SDone SVoid))) -> (CMember a' (Ident "index") True)
                 _ -> a'
         b'' = case typeOf a of
                 (SData _ (SPlus SDone (SPlus SDone SVoid))) -> (CMember b' (Ident "index") True)
                 _ -> b'
     boolIdent <- genIdent' "eq"

     declare sBool boolIdent
     putStat . CExpr . Just $   (CMember (CVar boolIdent) (Ident "index") True)
                            .=. (CCond (a'' .==. b'') (intE 0) (intE 1))

     return (CVar boolIdent)


flattenPrimOp (Less _) = \(a :* b :* End) ->
  do a' <- flattenABT a
     b' <- flattenABT b
     boolIdent <- genIdent' "less"

     declare sBool boolIdent
     putStat . CExpr . Just $   (CMember (CVar boolIdent) (Ident "index") True)
                            .=. (CCond (a' .<. b') (intE 0) (intE 1))

     return (CVar boolIdent)

flattenPrimOp t  = \_ -> error $ "TODO: flattenPrimOp: " ++ show t

----------------------------------------------------------------


flattenMeasureOp :: ( ABT Term abt
                    , typs ~ UnLCs args
                    , args ~ LCs typs)
                 => MeasureOp typs a
                 -> SArgs abt args
                 -> CodeGen CExpr
flattenMeasureOp Normal  = \(a :* b :* End) ->
  let randomE = (CCast doubleDecl rand)
              ./. (CCast doubleDecl (CVar . Ident $ "RAND_MAX")) in
  do a' <- flattenABT a
     b' <- flattenABT b

     uId <- genIdent
     declare SReal uId
     let varU = CVar uId

     vId <- genIdent
     declare SReal vId
     let varV = CVar vId

     rId <- genIdent
     let varR = CVar rId
     declare SReal rId


     doWhileCG ((varR .==. (intE 0)) .||. (varR .>. (intE 1)))
       $ do assign uId $ randomE .*. (floatE 2) .-. (floatE 1)
            assign vId $ randomE .*. (floatE 2) .-. (floatE 1)
            assign rId $ (varU .*. varU) .+. (varV .*. varV)

     cId <- genIdent
     declare SReal cId
     assign cId $ sqrt ((mkUnary "-" (intE 2)) .*. (log varR ./. varR))
     let varC = CVar cId
         value  = a' .+. (varU .*. (varC .*. ((expm1 b') .+. (intE 1))))

     (Sample sampleId _) <- getSample
     putSample (Sample sampleId value)
     return (intE 0)

flattenMeasureOp Uniform = \(a :* b :* End) ->
  do a' <- flattenABT a
     b' <- flattenABT b
     let r      = CCast doubleDecl rand
         rMax   = CCast doubleDecl (CVar . Ident $ "RAND_MAX")
         value  = (a' .+. ((r ./. rMax) .*. (b' .-. a')))
     (Sample sampleId _) <- getSample
     putSample (Sample sampleId value)
     return (intE 0)
flattenMeasureOp x = error $ "TODO: flattenMeasureOp: " ++ show x

----------------------------------------------------------------

flattenSuperpose
    :: (ABT Term abt)
    => NE.NonEmpty (abt '[] 'HProb, abt '[] ('HMeasure a))
    -> CodeGen CExpr

-- do we need to normalize?
flattenSuperpose wes =
  let wes' = NE.toList wes in

  if length wes' == 1
  then do _ <- flattenABT . snd . head $ wes'
          flattenABT . fst . head $ wes'
  else do weights <- mapM (flattenABT . fst) wes'

          -- compute sum of weights
          weightSumId <- genIdent' "wSum"
          declare SProb weightSumId
          assign weightSumId =<< (logSumExpCG $ S.fromList weights)
          let weightSum = CVar weightSumId

          -- draw number from uniform(0, weightSum)
          randId <- genIdent' "rand"
          declare SReal randId
          let r    = CCast doubleDecl rand
              rMax = CCast doubleDecl (CVar . Ident $ "RAND_MAX")
              rVar = CVar randId
          assign randId ((r ./. rMax) .*. (exp weightSum))


          outId <- genIdent
          declare SReal outId
          outLabel <- genIdent' "super"

          iterId <- genIdent' "it"
          declare SProb iterId
          let iter = CVar iterId

          -- try the first element
          assign iterId (head weights)
          stat <- runCodeGenBlock (do _ <- flattenABT (snd . head $ wes')
                                      (Sample _ e) <- getSample -- toss weight
                                      assign outId e
                                      putStat $ CGoto outLabel)
          putStat $ CIf (rVar .<. (exp iter)) stat Nothing


          forM_ (zip (tail weights) (fmap snd (tail wes'))) $ \(e,m) ->
            do assign iterId =<< (logSumExpCG $ S.fromList [iter, e])
               stat <- runCodeGenBlock (do _ <- flattenABT m -- toss weight
                                           (Sample _ e) <- getSample
                                           assign outId e
                                           putStat $ CGoto outLabel)
               putStat $ CIf (rVar .<. (exp iter)) stat Nothing

          putStat $ CLabel outLabel (CExpr Nothing)
          (Sample s _) <- getSample
          putSample (Sample s (CVar outId))
          return weightSum

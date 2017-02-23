# Data representation

Data types are stored using a sum of product representation.
They can be found in `Language.Hakaru.Syntax.Datum`.

````haskell
-- The first component is a hint for what the data constructor
-- should be called when pretty-printing, giving error messages,
-- etc. Like the hints for variable names, its value is not actually
-- used to decide which constructor is meant or which pattern
-- matches.
data Datum :: (Hakaru -> *) -> Hakaru -> * where
    Datum
        :: {-# UNPACK #-} !Text
        -> !(Sing (HData' t))
        -> !(DatumCode (Code t) ast (HData' t))
        -> Datum ast (HData' t)

-- | The intermediate components of a data constructor. The intuition
-- behind the two indices is that the @[[HakaruFun]]@ is a functor
-- applied to the Hakaru type. Initially the @[[HakaruFun]]@ functor
-- will be the 'Code' associated with the Hakaru type; hence it's
-- the one-step unrolling of the fixed point for our recursive
-- datatypes. But as we go along, we'll be doing induction on the
-- @[[HakaruFun]]@ functor.
data DatumCode :: [[HakaruFun]] -> (Hakaru -> *) -> Hakaru -> * where
    -- Skip rightwards along the sum.
    Inr :: !(DatumCode  xss abt a) -> DatumCode (xs ': xss) abt a
    -- Inject into the sum.
    Inl :: !(DatumStruct xs abt a) -> DatumCode (xs ': xss) abt a

data DatumStruct :: [HakaruFun] -> (Hakaru -> *) -> Hakaru -> * where
    -- BUG: haddock doesn't like annotations on GADT constructors
    -- <https://github.com/hakaru-dev/hakaru/issues/6>

    -- Combine components of the product. (\"et\" means \"and\" in Latin)
    Et  :: !(DatumFun    x         abt a)
        -> !(DatumStruct xs        abt a)
        ->   DatumStruct (x ': xs) abt a

    -- Close off the product.
    Done :: DatumStruct '[] abt a

data DatumFun :: HakaruFun -> (Hakaru -> *) -> Hakaru -> * where
    -- Hit a leaf which isn't a recursive component of the datatype.
    Konst :: !(ast b) -> DatumFun ('K b) ast a
    -- Hit a leaf which is a recursive component of the datatype.
    Ident :: !(ast a) -> DatumFun 'I     ast a
````

In Hakaru we have implemented Bool, Pair, Either, Maybe, and List.

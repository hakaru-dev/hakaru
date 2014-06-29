{-# LANGUAGE TypeFamilies, DataKinds, TypeOperators #-}
{-# OPTIONS -W #-}

module Util.HList where

class TList (xs :: [*]) where
  data VList (xs :: [*]) :: *
  type Append (xs :: [*]) (ys :: [*]) :: [*]
  append :: VList xs -> VList ys -> VList (Append xs ys)
  vsplit :: VList (Append xs ys) -> (VList xs, VList ys)

instance TList '[] where
  data VList '[] = VNil
  type Append '[] ys = ys
  append VNil ys = ys
  vsplit ys = (VNil, ys)

instance TList xs => TList (x ': xs) where
  data VList (x ': xs) = VCons x (VList xs)
  type Append (x ': xs) ys = x ': Append xs ys
  append (VCons x xs) ys = VCons x (append xs ys)
  vsplit (VCons x zs) = let (xs, ys) = vsplit zs in (VCons x xs, ys)

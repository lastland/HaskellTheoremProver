{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
    
module Basic where

data Bot 
data Top where
   One :: Top

data a :/\: b = AndT a b
data a :\/: b = OrT1 a | OrT2 b
data a :~>: b = ImpT (a -> b)

abort :: Bot -> a
abort x = case x of {}

data Nat = Z | S Nat deriving Eq

data TNat n where
   TZ :: TNat Z
   TS :: TNat n -> TNat (S n)

data HList :: [*] -> * where
  HNil  :: HList '[]
  HCons :: a -> HList t -> HList (a ': t)

type family (++) f g where
       '[]      ++ l2  = l2
       (a : as) ++ l2  = a : (as ++ l2)

infixr 1 :~>:
infixr 2 :\/:
infixr 3 :/\:

data Formula (a :: *) = MkFormula

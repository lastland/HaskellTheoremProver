{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds, TypeOperators #-}

module NatDedType where

import Text.PrettyPrint

data Bot
data a :/\: b = AndT a b
data a :\/: b = OrT a b
data a :~>: b = ImpT a b
data Nat = Ze | Succ Nat

infixl 1 :~>:
infixl 2 :\/:
infixl 3 :/\:

data Formula a where
     Contr :: Formula Bot
     And :: Formula a -> Formula b -> Formula (a :/\: b)
     Or  :: Formula a -> Formula b -> Formula (a :\/: b)
     Imp :: Formula a -> Formula b -> Formula (a :~>: b)

data Formulae = forall a. Formula a

data HList :: [*] -> * where
  HNil  :: HList '[]
  HCons :: a -> HList t -> HList (a ': t)

data Sequent b a = Seq (HList b) (Formula a)

x = Seq (HCons Contr HNil) Contr


type family MapR (f :: * -> *) (l :: [*]) :: [*] where
     MapR _ '[] = '[]
     MapR f (a ': as) = f a ': MapR f as 


type family MapL (f :: * -> *) (l :: [*]) :: [*]
type instance MapL f '[] = '[]
type instance MapL f (a : as) = f a : MapL f as
     
data Provable b a where
   Proof :: (HList b -> a) -> Provable b (Formula a)

data Prove (b :: [*]) a where
   Evd :: (HList b -> a) -> Prove (MapR Formula b) (Formula a)
   
data Derives b a where
  Ax1 :: Derives (a : b) a
  Ax2 :: Derives b a -> Derives (Formula c : b) a
  Ax3 :: Derives (b1 : b2 : btl) a -> Derives (b2 : b1 : btl) a
  AndI :: Derives b (Formula a1) -> Derives b (Formula a2)
                                 -> Derives b (Formula (a1 :/\: a2))
  AndE1 :: Derives b (Formula (a1 :/\: a2)) -> Derives b (Formula a1)
  AndE2 :: Derives b (Formula (a1 :/\: a2)) -> Derives b (Formula a2)
  OrI1  :: Derives b (Formula a1) -> Derives b (Formula (a1 :\/: a2))
  OrI2  :: Derives b (Formula a2) -> Derives b (Formula (a1 :\/: a2))
  OrE   :: Derives (Formula a1 : b) a -> Derives (Formula a2 : b) a
           -> Derives b (Formula (a1 :\/: a2)) -> Derives b a
  ImpI :: Derives (Formula a : b) (Formula c) -> Derives b (Formula (a :~>: c))
  ImpE :: Derives b (Formula (a :~>: c)) -> Derives b (Formula a)
                                         -> Derives b (Formula c)

thm :: Derives (Formula Bot : '[]) (Formula Bot)
thm = Ax1

thm2 :: Derives (Formula (Bot :/\: (Bot :~>: Bot)) : '[])
                (Formula ((Bot :~>: Bot) :/\: Bot))
thm2 = AndI (AndE2 Ax1) (AndE1 Ax1)

thm2' :: Provable ((Bot :/\: (Bot :~>: Bot)) : '[])
                (Formula ((Bot :~>: Bot) :/\: Bot))
thm2' = Proof $ \x -> case x of
                       (HCons (AndT p1 p2) HNil) -> AndT p2 p1 

{-
thm3 :: Prove (Formula (Bot :/\: (Bot :~>: Bot)) : '[])
                (Formula ((Bot :~>: Bot) :/\: Bot))
thm3 = Evd $ \x -> case x of
                       __ -> AndT _ _
-}

    

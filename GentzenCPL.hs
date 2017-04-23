{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}


module CPL where

import           Control.Monad
import           Data.Singletons
import           Data.Singletons.Prelude.List ((:++), SList)
import qualified Data.Singletons.Prelude.List as S
import           Data.Singletons.TH
import           ProofTree
import           Text.PrettyPrint

data Atom :: * where
  A :: Atom
  B :: Atom
  C :: Atom
  deriving (Show, Eq)

data Formula :: * where
  Truth :: Formula
  Not :: Formula -> Formula
  And :: Formula -> Formula -> Formula
  Or  :: Formula -> Formula -> Formula
  Imp :: Formula -> Formula -> Formula
  Var :: Atom -> Formula
  deriving (Show, Eq)

$(genSingletons[''Atom, ''Formula])

data Derives :: [Formula] -> [Formula] -> * where
  T      :: Seqt gamma => Derives gamma '[Truth]
  I      :: Seqt a => Derives '[a] '[a]
  Cut    :: (Seqt a, Seqt gamma, Seqt sigma, Seqt delta, Seqt pi) =>
            Derives gamma (a:delta) ->
            Derives (a:sigma) pi ->
            Derives (gamma :++ sigma) (delta :++ pi)
  LConj1 :: (Seqt a, Seqt b, Seqt gamma, Seqt delta) =>
            Derives (a:gamma) delta ->
            Derives ((And a b):gamma) delta
  LConj2 :: (Seqt a, Seqt b, Seqt gamma, Seqt delta) =>
            Derives (b:gamma) delta ->
            Derives ((And a b):gamma) delta
  LDisj  :: (Seqt a, Seqt b, Seqt gamma, Seqt delta, Seqt sigma, Seqt pi) =>
            Derives (a:gamma) delta ->
            Derives (b:sigma) pi ->
            Derives ((Or a b):(gamma :++ sigma)) (delta :++ pi)
  LImp   :: (Seqt a, Seqt b, Seqt gamma, Seqt delta, Seqt sigma, Seqt pi) =>
            Derives (gamma) (a:delta) ->
            Derives (b:sigma) pi ->
            Derives ((Imp a b):(gamma :++ sigma)) (delta :++ pi)
  LNot   :: (Seqt a, Seqt gamma, Seqt delta)  =>
            Derives gamma (a:delta) ->
            Derives ((Not a):gamma) delta
  RDisj1 :: (Seqt a, Seqt b, Seqt gamma, Seqt delta) =>
            Derives gamma (a:delta) ->
            Derives gamma ((Or a b):delta)
  RDisj2 :: (Seqt a, Seqt b, Seqt gamma, Seqt delta) =>
            Derives gamma (b:delta) ->
            Derives gamma ((Or a b):delta)
  RConj  :: (Seqt a, Seqt b, Seqt gamma, Seqt delta, Seqt sigma, Seqt pi) =>
            Derives gamma (a:delta) ->
            Derives sigma (b:pi) ->
            Derives (gamma :++ sigma) ((And a b):(delta :++ pi))
  RImp   :: (Seqt a, Seqt b, Seqt gamma, Seqt delta) =>
            Derives (a:gamma) (b:delta) ->
            Derives gamma ((Imp a b):delta)
  RNot   :: (Seqt a, Seqt gamma, Seqt delta) =>
            Derives (a:gamma) delta ->
            Derives gamma ((Not a):delta)
  LW     :: (Seqt a, Seqt gamma, Seqt delta) =>
            Derives gamma delta ->
            Derives (a:gamma) delta
  CL     :: (Seqt a, Seqt gamma, Seqt delta) =>
            Derives (a:a:gamma) delta ->
            Derives (a:gamma) delta
  PL     :: (Seqt a, Seqt b, Seqt gamma, Seqt delta, Seqt sigma,
             Seqt (sigma :++ a:b:gamma)) =>
            Derives '[a] '[a] ->
            Derives '[b] '[b] ->
            Derives sigma '[Truth] ->
            Derives gamma '[Truth] ->
            Derives (sigma :++ a:b:gamma) delta ->
            Derives (sigma :++ b:a:gamma) delta
  WR     :: (Seqt a, Seqt gamma, Seqt delta) =>
            Derives gamma delta ->
            Derives gamma (a:delta)
  CR     :: (Seqt a, Seqt gamma, Seqt delta) =>
            Derives gamma (a:a:delta) ->
            Derives gamma (a:delta)
  PR     :: (Seqt a, Seqt b, Seqt gamma, Seqt delta, Seqt sigma,
             Seqt (sigma :++ a:b:gamma)) =>
            Derives '[a] '[a] ->
            Derives '[b] '[b] ->
            Derives sigma '[Truth] ->
            Derives gamma '[Truth] ->
            Derives delta (sigma :++ a:b:gamma) ->
            Derives delta (sigma :++ b:a:gamma)

class SingI gamma => Seqt (gamma :: k) where
  ppt :: Sing gamma -> String

instance Seqt (Var A) where
  ppt _ = "A"

instance Seqt (Var B) where
  ppt _ = "B"

instance Seqt (Var C) where
  ppt _ = "C"

instance Seqt a => Seqt (Not a) where
  ppt (SNot a@(SVar _)) = "~" ++ ppt a
  ppt (SNot a)          = "~(" ++ ppt a ++ ")"

instance (Seqt a, Seqt b) => Seqt (And a b) where
  ppt (SAnd a b) = ppt a ++ " /\\ " ++ ppt b

instance (Seqt a, Seqt b) => Seqt (Or a b) where
  ppt (SOr a b) = ppt a ++ " \\/ " ++ ppt b

instance (Seqt a, Seqt b) => Seqt (Imp a b) where
  ppt (SImp a b) = ppt a ++ " -> " ++ ppt b

instance Seqt ('[]) where
  ppt (S.SNil)       = ""

instance (Seqt a, Seqt as) => Seqt (a ': as) where
  ppt (S.SCons a S.SNil) = ppt a
  ppt (S.SCons a as)     = (ppt a) ++ ", " ++ (ppt as)


pp :: forall gamma delta. (Seqt gamma, Seqt delta) =>
  Derives gamma delta -> ProofTree
pp theorem = l $ g ++ " |- " ++ d
  where
  l x = pNode x xs
  xs = case theorem of
    I            -> []
    Cut a b      -> [pp a,  pp b]
    LConj1 a     -> [pp a]
    LConj2 a     -> [pp a]
    LDisj a b    -> [pp a, pp b]
    LImp a b     -> [pp a, pp b]
    LNot a       -> [pp a]
    RDisj1 a     -> [pp a]
    RDisj2 a     -> [pp a]
    RConj a b    -> [pp a, pp b]
    RImp a       -> [pp a]
    RNot a       -> [pp a]
    LW a         -> [pp a]
    CL a         -> [pp a]
    PL _ _ _ _ a -> [pp a]
    WR a         -> [pp a]
    CR a         -> [pp a]
    PR _ _ _ _ a -> [pp a]
  g = ppt (sing :: Sing gamma)
  d = ppt (sing :: Sing delta)

simple :: Derives '[Var A] '[Var A]
simple = I

empDerTr :: Derives '[] '[Truth]
empDerTr = T

flipCtx :: (Seqt a, Seqt b, Seqt c, Seqt d) =>
  Derives (a ': b ': c) d -> Derives (b ': a ': c) d
flipCtx = PL I I empDerTr T

flipDer :: (Seqt a, Seqt b, Seqt c, Seqt d) =>
  Derives a (b ': c ': d) -> Derives a (c ': b ': d)
flipDer = PR I I empDerTr T

doubNegP1 :: Seqt p => Derives '[Not (Not p)] '[p]
doubNegP1 = LNot $ RNot I

-- notTandFP :: forall p q. (Seqt p, Seqt q) =>
--  Derives '[And p (Not p)] '[q]
-- notTandFP = undefined

derMorIntP :: forall p q. (Seqt p, Seqt q) =>
  Derives '[Not (Or p q)] '[And (Not p) (Not q)]
derMorIntP = LNot (CR f) where
  f :: Derives '[] '[Or p q, Or p q, And (Not p) (Not q)]
  f = PR I I (T :: Derives '[Or p q] '[Truth]) T $ flipDer g
  g :: Derives '[] '[And (Not p) (Not q), Or p q, Or p q]
  g = RConj (flipDer . RDisj1 . flipDer . RNot $ I)
      (flipDer . RDisj2 . flipDer . RNot $ I)

derMorIntA :: Derives '[Not (Or (Var A) (Var B))]
  '[And (Not (Var A)) (Not (Var B))]
derMorIntA = derMorIntP

--notTandFA :: Derives '[And p (Not p)] '[p]
--notTandFA = undefined

excludedMiddleP :: Seqt a => Derives '[] '[Or a (Not a)]
excludedMiddleP = CR . RDisj1 . flipDer . RDisj2 . RNot $ I

excludedMiddleA :: Derives '[] '[Or (Var A) (Not (Var A))]
excludedMiddleA = excludedMiddleP

disjCommP :: (Seqt p, Seqt q) => Derives '[Or p q] '[Or q p]
disjCommP = CR (LDisj (RDisj2 I) (RDisj1 I))

disjCommA :: Derives '[Or (Var A) (Var B)] '[Or (Var B) (Var A)]
disjCommA = disjCommA

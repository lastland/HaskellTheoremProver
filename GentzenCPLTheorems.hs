{-# LANGUAGE ScopedTypeVariables #-}

module GentzenCPLTheorems where

import Gentzen
import GentzenCPL
import ProofTree

simple :: Derives '[Var A] '[Var A]
simple = I

empDerTr :: Derives '[] '[Top]
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
  f = PR I I (T :: Derives '[Or p q] '[Top]) T $ flipDer g
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

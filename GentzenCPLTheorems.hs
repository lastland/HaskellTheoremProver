{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}

module GentzenCPLTheorems where

import           Gentzen
import           GentzenCPL
import           ProofTree

simple :: Derives '[VA] '[VA]
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
  Derives '[Not (p \/ q)] '[Not p /\ Not q]
derMorIntP = LNot (CR f) where
  f :: Derives '[] '[p \/ q, p \/ q, Not p /\ Not q]
  f = PR I I (T :: Derives '[p \/ q] '[Top]) T $ flipDer g
  g :: Derives '[] '[Not p /\ Not q, p \/ q, p \/ q]
  g = RConj (flipDer . RDisj1 . flipDer . RNot $ I)
      (flipDer . RDisj2 . flipDer . RNot $ I)

derMorIntA :: Derives '[Not (VA \/ VB)] '[Not VA /\ Not VB]
derMorIntA = derMorIntP

--notTandFA :: Derives '[And p (Not p)] '[p]
--notTandFA = undefined

excludedMiddleP :: Seqt a => Derives '[] '[a \/ Not a]
excludedMiddleP = CR . RDisj1 . flipDer . RDisj2 . RNot $ I

excludedMiddleA :: Derives '[] '[VA \/ Not VA]
excludedMiddleA = excludedMiddleP

disjCommP :: (Seqt p, Seqt q) => Derives '[p \/ q] '[q \/ p]
disjCommP = CR (LDisj (RDisj2 I) (RDisj1 I))

disjCommA :: Derives '[VA \/ VB] '[VB \/ VA]
disjCommA = disjCommA

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}

module FmlKind.GentzenCPLTheorems where

import           FmlKind.Basic
import           FmlKind.GentzenCPL
import           Printing.ProofTree

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

doubNeg1 :: Seqt p => Derives '[Not (Not p)] '[p]
doubNeg1 = LNot $ RNot I

doubNeg1' :: Derives '[Not (Not VA)] '[VA]
doubNeg1' = LNot $ RNot I


-- notTandFP :: forall p q. (Seqt p, Seqt q) =>
--  Derives '[And p (Not p)] '[q]
-- notTandFP = undefined

deMorInt :: forall p q. (Seqt p, Seqt q) =>
  Derives '[Not (p \/ q)] '[Not p /\ Not q]
deMorInt = LNot (CR f) where
  f :: Derives '[] '[p \/ q, p \/ q, Not p /\ Not q]
  f = PR I I (T :: Derives '[p \/ q] '[Top]) T $ flipDer g
  g :: Derives '[] '[Not p /\ Not q, p \/ q, p \/ q]
  g = RConj (flipDer . RDisj1 . flipDer . RNot $ I)
      (flipDer . RDisj2 . flipDer . RNot $ I)

deMorInt' :: Derives '[Not (VA \/ VB)] '[Not VA /\ Not VB]
deMorInt' = deMorInt

--notTandFA :: Derives '[And p (Not p)] '[p]
--notTandFA = undefined

excludedMiddle :: Seqt a => Derives '[] '[a \/ Not a]
excludedMiddle = CR . RDisj1 . flipDer . RDisj2 . RNot $ I

excludedMiddle' :: Derives '[] '[VA \/ Not VA]
excludedMiddle' = excludedMiddle

disjComm :: (Seqt p, Seqt q) => Derives '[p \/ q] '[q \/ p]
disjComm = CR (LDisj (RDisj2 I) (RDisj1 I))

disjComm' :: Derives '[VA \/ VB] '[VB \/ VA]
disjComm' = disjComm

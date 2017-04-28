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

-- ~(~P) |- P
doubNeg1 :: Seqt p => Derives '[Not (Not p)] '[p]
doubNeg1 = LNot $ RNot I

-- ~(~P) |- P (can be printed)
doubNeg1' :: Derives '[Not (Not VA)] '[VA]
doubNeg1' = LNot $ RNot I

-- ~(P \/ Q) |- ~P /\ ~Q
deMorInt :: forall p q. (Seqt p, Seqt q) =>
  Derives '[Not (p \/ q)] '[Not p /\ Not q]
deMorInt = LNot (CR f) where
  f :: Derives '[] '[p \/ q, p \/ q, Not p /\ Not q]
  f = PR I I (T :: Derives '[p \/ q] '[Top]) T $ flipDer g
  g :: Derives '[] '[Not p /\ Not q, p \/ q, p \/ q]
  g = RConj (flipDer . RDisj1 . flipDer . RNot $ I)
      (flipDer . RDisj2 . flipDer . RNot $ I)

-- ~(P \/ Q) |- ~P /\ ~Q (can be printed)
deMorInt' :: Derives '[Not (VA \/ VB)] '[Not VA /\ Not VB]
deMorInt' = deMorInt

--  |- P \/ ~P
excludedMiddle :: Seqt a => Derives '[] '[a \/ Not a]
excludedMiddle = CR . RDisj1 . flipDer . RDisj2 . RNot $ I

--  |- P \/ ~P (can be printed)
excludedMiddle' :: Derives '[] '[VA \/ Not VA]
excludedMiddle' = excludedMiddle

-- P \/ Q |- Q \/ P
disjComm :: (Seqt p, Seqt q) => Derives '[p \/ q] '[q \/ p]
disjComm = CR (LDisj (RDisj2 I) (RDisj1 I))

-- P \/ Q |- Q \/ P (can be printed)
disjComm' :: Derives '[VA \/ VB] '[VB \/ VA]
disjComm' = disjComm

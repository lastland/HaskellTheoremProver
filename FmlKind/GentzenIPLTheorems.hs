{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}

module FmlKind.GentzenIPLTheorems where

import           FmlKind.Gentzen
import           FmlKind.GentzenIPL
import           Printing.ProofTree

simple :: Derives '[VA] VA
simple = I

empDerTr :: Derives '[] Top
empDerTr = T

flipCtx :: (Seqt a, Seqt b, Seqt c, Seqt d) =>
  Derives (a ': b ': c) d -> Derives (b ': a ': c) d
flipCtx = PL I I empDerTr T

_notTandF :: (Seqt p, Seqt q) => Derives '[p, Not p] q
_notTandF = flipCtx . F $ LNot I

notTandF :: (Seqt p, Seqt q) => Derives '[p /\ Not p] q
notTandF = LConj _notTandF

notTandF' :: Derives '[VA /\ Not VA] VB
notTandF' = notTandF

andFlip :: (Seqt p, Seqt q) => Derives '[p /\ q] (q /\ p)
andFlip = RConj (LConj $ LW I) (LConj $ flipCtx $ LW I)

andFlip' :: Derives '[VA /\ VB] (VB /\ VA)
andFlip' = andFlip

orFlip :: (Seqt p, Seqt q) => Derives '[p \/ q] (q \/ p)
orFlip = LDisj (RDisj2 I) (RDisj1 I)

orFlip' :: Derives '[VA \/ VB] (VB \/ VA)
orFlip' = orFlip

distr1 :: (Seqt p, Seqt q, Seqt r) =>
  Derives '[p /\ (q \/ r)] ((p /\ q) \/ (p /\ r))
distr1 = LConj $ flipCtx $ LDisj a b where
  a = RDisj1 $ flipCtx $ RConj (flipCtx $ LW I) (LW I)
  b = RDisj2 $ flipCtx $ RConj (flipCtx $ LW I) (LW I)

distr1' :: Derives '[VA /\ (VB \/ VC)] ((VA /\ VB) \/ (VA /\ VC))
distr1' = distr1

distr2 :: (Seqt p, Seqt q, Seqt r) =>
  Derives '[(p /\ q) \/ (p /\ r)] (p /\ (q \/ r))
distr2 = LDisj (LConj a) (LConj b) where
  a = RConj (flipCtx $ LW I) (RDisj1 $ LW I)
  b = RConj (flipCtx $ LW I) (RDisj2 $ LW I)

distr2' :: Derives '[(VA /\ VB) \/ (VA /\ VC)] (VA /\ (VB \/ VC))
distr2' = distr2

impTrans :: forall p q r .(Seqt p, Seqt q, Seqt r) =>
  Derives '[p ~> (q ~> r), p ~> q] (p ~> r)
impTrans = flipCtx . RImp . flipCtx $ LImp (flipCtx $ LW I) f where
  f :: Derives '[q, p, p ~> (q ~> r)] r
  f = PL I I t T . flipCtx $ LImp (LW I) g
  g :: Derives '[q ~> r, q, p] r
  g = LImp (flipCtx $ LW I)
      (flipCtx . PL I I t T . LW $ LW I)
  t :: Derives '[q] Top
  t = T

impTrans' :: Derives '[VA ~> (VB ~> VC), VA ~> VB] (VA ~> VC)
impTrans' = impTrans

doubleNegImp :: Seqt p => Derives '[p] (Not (Not p))
doubleNegImp = RNot $ LNot I

doubleNegImp' :: Derives '[VA] (Not (Not VA))
doubleNegImp' = doubleNegImp

derMorgan1 :: (Seqt p, Seqt q) =>
  Derives '[Not (p \/ q)] (Not p /\ Not q)
derMorgan1 = RConj (RNot . flipCtx . LNot $ RDisj1 I)
            (RNot . flipCtx . LNot $ RDisj2 I)

derMorgan1' :: Derives '[Not (VA \/ VB)] (Not VA /\ Not VB)
derMorgan1' = derMorgan1

derMorgan2 :: forall p q .(Seqt p, Seqt q) =>
  Derives '[Not p /\ Not q] (Not (p \/ q))
derMorgan2 = LConj . RNot $ LDisj f g where
  f :: Derives '[p, Not p, Not q] Bottom
  f = PL I I (T :: Derives '[p] Top) T . flipCtx $ LW _notTandF
  g :: Derives '[q, Not p, Not q] Bottom
  g = flipCtx $ LW _notTandF

derMorgan2' :: Derives '[Not VA /\ Not VB] (Not (VA \/ VB))
derMorgan2' = derMorgan2

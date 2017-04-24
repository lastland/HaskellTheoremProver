{-# LANGUAGE ScopedTypeVariables #-}

module GentzenIPLTheorems where

import           Gentzen
import           GentzenIPL
import           ProofTree

simple :: Derives '[VA] VA
simple = I

empDerTr :: Derives '[] Top
empDerTr = T

flipCtx :: (Seqt a, Seqt b, Seqt c, Seqt d) =>
  Derives (a ': b ': c) d -> Derives (b ': a ': c) d
flipCtx = PL I I empDerTr T

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

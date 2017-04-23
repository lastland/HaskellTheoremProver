{-# LANGUAGE ScopedTypeVariables #-}

module GentzenIPLTheorems where

import           Gentzen
import           GentzenIPL
import           ProofTree

simple :: Derives '[Var A] (Var A)
simple = I

empDerTr :: Derives '[] Top
empDerTr = T

flipCtx :: (Seqt a, Seqt b, Seqt c, Seqt d) =>
  Derives (a ': b ': c) d -> Derives (b ': a ': c) d
flipCtx = PL I I empDerTr T

andFlip :: (Seqt p, Seqt q) => Derives '[And p q] (And q p)
andFlip = RConj (LConj $ LW I) (LConj $ flipCtx $ LW I)

andFlip' :: Derives '[And (Var A) (Var B)] (And (Var B) (Var A))
andFlip' = andFlip

orFlip :: (Seqt p, Seqt q) => Derives '[Or p q] (Or q p)
orFlip = LDisj (RDisj2 I) (RDisj1 I)

orFlip' :: Derives '[Or (Var A) (Var B)] (Or (Var B) (Var A))
orFlip' = orFlip

distr1 :: (Seqt p, Seqt q, Seqt r) =>
  Derives '[And p (Or q r)] (Or (And p q) (And p r))
distr1 = LConj $ flipCtx $ LDisj a b where
  a = RDisj1 $ flipCtx $ RConj (flipCtx $ LW I) (LW I)
  b = RDisj2 $ flipCtx $ RConj (flipCtx $ LW I) (LW I)

distr1' :: Derives '[And (Var A) (Or (Var B) (Var C))]
  (Or (And (Var A) (Var B)) (And (Var A) (Var C)))
distr1' = distr1

distr2 :: (Seqt p, Seqt q, Seqt r) =>
  Derives '[Or (And p q) (And p r)] (And p (Or q r))
distr2 = LDisj (LConj a) (LConj b) where
  a = RConj (flipCtx $ LW I) (RDisj1 $ LW I)
  b = RConj (flipCtx $ LW I) (RDisj2 $ LW I)

distr2' :: Derives '[Or (And (Var A) (Var B)) (And (Var A) (Var C))]
  (And (Var A) (Or (Var B) (Var C)))
distr2' = distr2

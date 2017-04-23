{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}

module GentzenIPL where

import           Data.Singletons
import           Data.Singletons.Prelude.List ((:++))
import           Gentzen
import           ProofTree

data Derives :: [Formula] -> Formula -> * where
  T      :: Seqt gamma => Derives gamma Top
  F      :: (Seqt a, Seqt gamma) =>
            Derives gamma Bottom ->
            Derives gamma a
  I      :: Seqt a => Derives '[a] a
  LConj  :: (Seqt a, Seqt b, Seqt gamma, Seqt delta) =>
            Derives (a:b:gamma) delta ->
            Derives (And a b:gamma) delta
  LDisj  :: (Seqt a, Seqt b, Seqt gamma, Seqt delta) =>
            Derives (a:gamma) delta ->
            Derives (b:gamma) delta ->
            Derives (Or a b:gamma) delta
  LImp   :: (Seqt a, Seqt b, Seqt gamma, Seqt delta) =>
            Derives gamma a ->
            Derives (b:gamma) delta ->
            Derives (Imp a b:gamma) delta
  LNot   :: (Seqt a, Seqt gamma) =>
            Derives gamma a ->
            Derives (Not a:gamma) Bottom
  RDisj1 :: (Seqt a, Seqt b, Seqt gamma) =>
            Derives gamma a ->
            Derives gamma (Or a b)
  RDisj2 :: (Seqt a, Seqt b, Seqt gamma) =>
            Derives gamma b ->
            Derives gamma (Or a b)
  RConj  :: (Seqt a, Seqt b, Seqt gamma) =>
            Derives gamma a ->
            Derives gamma b ->
            Derives gamma (And a b)
  RImp   :: (Seqt a, Seqt b, Seqt gamma) =>
            Derives (a:gamma) b ->
            Derives gamma (Imp a b)
  RNot   :: (Seqt a, Seqt gamma) =>
            Derives (a:gamma) Bottom ->
            Derives gamma (Not a)
  LW     :: (Seqt a, Seqt gamma, Seqt delta) =>
            Derives gamma delta ->
            Derives (a:gamma) delta
  CL     :: (Seqt a, Seqt gamma, Seqt delta) =>
            Derives (a:a:gamma) delta ->
            Derives (a:gamma) delta
  PL     :: (Seqt a, Seqt b, Seqt gamma, Seqt delta, Seqt sigma,
             Seqt (sigma :++ a:b:gamma)) =>
            Derives '[a] a ->
            Derives '[b] b ->
            Derives sigma Top ->
            Derives gamma Top ->
            Derives (sigma :++ a:b:gamma) delta ->
            Derives (sigma :++ b:a:gamma) delta


pp :: forall gamma delta. (Seqt gamma, Seqt delta) =>
  Derives gamma delta -> ProofTree
pp theorem = l $ g ++ " |- " ++ d
  where
  l x = pNode x xs
  xs = case theorem of
    I            -> []
    LConj a      -> [pp a]
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
  g = ppt (sing :: Sing gamma)
  d = ppt (sing :: Sing delta)

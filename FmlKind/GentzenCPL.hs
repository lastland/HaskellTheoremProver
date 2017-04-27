{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}

module FmlKind.GentzenCPL where

import           Data.Singletons              (Sing, sing)
import           Data.Singletons.Prelude.List ((:++))
import           Gentzen
import           Printing.ProofTree

data Derives :: [Formula] -> [Formula] -> * where
  T      :: Seqt gamma => Derives gamma '[Top]
  I      :: Seqt a => Derives '[a] '[a]
  Cut    :: (Seqt a, Seqt gamma, Seqt sigma, Seqt delta, Seqt pi) =>
            Derives gamma (a:delta) ->
            Derives (a:sigma) pi ->
            Derives (gamma :++ sigma) (delta :++ pi)
  LConj1 :: (Seqt a, Seqt b, Seqt gamma, Seqt delta) =>
            Derives (a:gamma) delta ->
            Derives (a /\ b:gamma) delta
  LConj2 :: (Seqt a, Seqt b, Seqt gamma, Seqt delta) =>
            Derives (b:gamma) delta ->
            Derives (a /\ b:gamma) delta
  LDisj  :: (Seqt a, Seqt b, Seqt gamma, Seqt delta, Seqt sigma, Seqt pi) =>
            Derives (a:gamma) delta ->
            Derives (b:sigma) pi ->
            Derives (a \/ b:(gamma :++ sigma)) (delta :++ pi)
  LImp   :: (Seqt a, Seqt b, Seqt gamma, Seqt delta, Seqt sigma, Seqt pi) =>
            Derives gamma (a:delta) ->
            Derives (b:sigma) pi ->
            Derives (a ~> b:(gamma :++ sigma)) (delta :++ pi)
  LNot   :: (Seqt a, Seqt gamma, Seqt delta)  =>
            Derives gamma (a:delta) ->
            Derives (Not a:gamma) delta
  RDisj1 :: (Seqt a, Seqt b, Seqt gamma, Seqt delta) =>
            Derives gamma (a:delta) ->
            Derives gamma (a \/ b:delta)
  RDisj2 :: (Seqt a, Seqt b, Seqt gamma, Seqt delta) =>
            Derives gamma (b:delta) ->
            Derives gamma (a \/ b:delta)
  RConj  :: (Seqt a, Seqt b, Seqt gamma, Seqt delta, Seqt sigma, Seqt pi) =>
            Derives gamma (a:delta) ->
            Derives sigma (b:pi) ->
            Derives (gamma :++ sigma) (a /\ b:(delta :++ pi))
  RImp   :: (Seqt a, Seqt b, Seqt gamma, Seqt delta) =>
            Derives (a:gamma) (b:delta) ->
            Derives gamma (a ~> b:delta)
  RNot   :: (Seqt a, Seqt gamma, Seqt delta) =>
            Derives (a:gamma) delta ->
            Derives gamma (Not a:delta)
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
            Derives sigma '[Top] ->
            Derives gamma '[Top] ->
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
            Derives sigma '[Top] ->
            Derives gamma '[Top] ->
            Derives delta (sigma :++ a:b:gamma) ->
            Derives delta (sigma :++ b:a:gamma)

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

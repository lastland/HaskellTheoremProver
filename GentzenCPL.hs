{-# LANGUAGE DataKinds           #-}
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
import           Text.PrettyPrint

data Atom :: * where
  A :: Atom
  B :: Atom
  C :: Atom
  deriving (Show, Eq)

data Formula :: * where
  Not :: Formula -> Formula
  And :: Formula -> Formula -> Formula
  Or  :: Formula -> Formula -> Formula
  Imp :: Formula -> Formula -> Formula
  Var :: Atom -> Formula
  deriving (Show, Eq)

$(genSingletons[''Atom, ''Formula])

data Derives :: [Formula] -> [Formula] -> * where
  I      :: SingI a => Derives '[a] '[a]
  Cut    :: SingI a =>
            Derives gamma (a:delta) ->
            Derives (a:sigma) pi ->
            Derives (gamma :++ sigma) (delta :++ pi)
  LConj1 :: SingI b =>
            Derives (a:gamma) delta ->
            Derives ((And a b):gamma) delta
  LConj2 :: SingI a =>
            Derives (b:gamma) delta ->
            Derives ((And a b):gamma) delta
  LDisj  :: Derives (a:gamma) delta ->
            Derives (b:sigma) pi ->
            Derives ((Or a b):(gamma :++ sigma)) (delta :++ pi)
  LImp   :: Derives (gamma) (a:delta) ->
            Derives (b:sigma) pi ->
            Derives ((Imp a b):(gamma :++ sigma)) (delta :++ pi)
  LNot   :: SingI a =>
            Derives gamma delta ->
            Derives ((Not a):gamma) delta
  RDisj1 :: SingI b =>
            Derives gamma (a:delta) ->
            Derives gamma ((Or a b):delta)
  RDisj2 :: SingI a =>
            Derives gamma (b:delta) ->
            Derives gamma ((Or a b):delta)
  RConj  :: Derives gamma (a:delta) ->
            Derives sigma (b:pi) ->
            Derives (gamma :++ sigma) ((And a b):(delta :++ pi))
  RImp   :: Derives (a:gamma) (b:delta) ->
            Derives gamma ((Imp a b):delta)
  RNot   :: Derives (a:gamma) delta ->
            Derives gamma ((Not a):delta)
  LW     :: SingI a =>
            Derives gamma delta ->
            Derives (a:gamma) delta
  CL     :: Derives (a:a:gamma) delta ->
            Derives (a:gamma) delta
  PL     :: Derives (a:b:gamma) delta ->
            Derives (b:a:gamma) delta
  WR     :: Derives gamma delta ->
            Derives gamma (a:delta)
  CR     :: Derives gamma (a:a:delta) ->
            Derives gamma (a:delta)
  PR     :: Derives gamma (a:b:delta) ->
            Derives gamma (b:a:delta)

class PPT (gamma :: k) where
  ppt :: Sing gamma -> String

instance PPT (Var A) where
  ppt _ = "A"

instance PPT (Var B) where
  ppt _ = "B"

instance PPT (Var C) where
  ppt _ = "C"

instance PPT a => PPT (Not a) where
  ppt (SNot a) = "~" ++ ppt a

instance (PPT a, PPT b) => PPT (And a b) where
  ppt (SAnd a b) = ppt a ++ " /\\ " ++ ppt b

instance (PPT a, PPT b) => PPT (Or a b) where
  ppt (SOr a b) = ppt a ++ " \\/ " ++ ppt b

instance (PPT a, PPT b) => PPT (Imp a b) where
  ppt (SImp a b) = ppt a ++ " -> " ++ ppt b

instance PPT ('[]) where
  ppt (S.SNil)       = "empty"

instance (PPT a, PPT as) => PPT (a ': as) where
  ppt (S.SCons a S.SNil) = ppt a
  ppt (S.SCons a as)     = (ppt a) ++ ", " ++ (ppt as)

pp :: forall gamma delta. (PPT gamma, SingI gamma, PPT delta, SingI delta) =>
  Derives gamma delta -> String
pp theorem = g ++ " |- " ++ d where
  g = ppt (sing :: Sing gamma)
  d = ppt (sing :: Sing delta)

type Sequent = ([Formula], [Formula])

va = SVar SA
vb = SVar SB
vc = SVar SC
neg = SNot

simple :: Derives '[Var A] '[Var A]
simple = I

excludedMiddle :: Derives '[] '[Or (Var A) (Not (Var A))]
excludedMiddle = CR . RDisj1 . PR . RDisj2 . RNot $ I

disjComm :: Derives '[] '[Imp (Or (Var A) (Var B))
                           (Or (Var B) (Var A))]
disjComm = RImp (CR (LDisj (RDisj2 I) (RDisj1 I)))

printExcludedMiddle :: IO (Derives '[] '[Or (Var A) (Not (Var A))])
printExcludedMiddle = let a = I
                          b = RNot a
                          c = RDisj2 b
                          d = PR c
                          e = RDisj1 d
                          f = CR e in
                        putStrLn "------------" >>
                        putStrLn (pp a) >>
                        putStrLn "------------" >>
                        putStrLn (pp b) >>
                        putStrLn "------------" >>
                        putStrLn (pp c) >>
                        putStrLn "------------" >>
                        putStrLn (pp d) >>
                        putStrLn "------------" >>
                        putStrLn (pp e) >>
                        putStrLn "------------" >>
                        putStrLn (pp f) >>
                        return f

{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE KindSignatures    #-}
{-# LANGUAGE PolyKinds         #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeFamilies      #-}
{-# LANGUAGE TypeOperators     #-}

module FmlKind.Basic where

import           Data.Singletons
import qualified Data.Singletons.Prelude.List as S
import           Data.Singletons.TH


data Atom :: * where
  A :: Atom
  B :: Atom
  C :: Atom
  deriving (Show, Eq)

data Formula :: * where
  Top    :: Formula
  Bottom :: Formula
  Not :: Formula -> Formula
  And :: Formula -> Formula -> Formula
  Or  :: Formula -> Formula -> Formula
  Imp :: Formula -> Formula -> Formula
  Var :: Atom -> Formula
  deriving (Show, Eq)

$(genSingletons[''Atom, ''Formula])

type (/\) = And
type (\/) = Or
type (~>) = Imp

type VA = Var A
type VB = Var B
type VC = Var C

class SingI gamma => Seqt (gamma :: k) where
  ppt :: Sing gamma -> String

instance Seqt (Var A) where
  ppt _ = "A"

instance Seqt (Var B) where
  ppt _ = "B"

instance Seqt (Var C) where
  ppt _ = "C"

instance Seqt Top where
  ppt _ = "⊤"

instance Seqt Bottom where
  ppt _ = "⊥"

instance Seqt a => Seqt (Not a) where
  ppt e@(SNot a) = "~" ++ lp (<=) a e ++ ""

instance (Seqt a, Seqt b) => Seqt (And a b) where
  ppt e@(SAnd a b) = lp (<=) a e ++ " /\\ " ++ lp (<) b e where

instance (Seqt a, Seqt b) => Seqt (Or a b) where
  ppt e@(SOr a b) = lp (<=) a e ++ " \\/ " ++ lp (<) b e

instance (Seqt a, Seqt b) => Seqt (Imp a b) where
  ppt e@(SImp a b) = lp (<=) a e ++ " -> " ++ lp (<) b e

instance Seqt ('[]) where
  ppt (S.SNil)       = ""

instance (Seqt a, Seqt as) => Seqt (a ': as) where
  ppt (S.SCons a S.SNil) = ppt a
  ppt (S.SCons a as)     = (ppt a) ++ ", " ++ (ppt as)

level :: forall (a :: Formula). Seqt a => Sing a -> Int
level (SVar _)   = 100
level STop       = 100
level SBottom    = 100
level (SNot _)   = 10
level (SAnd _ _) = 8
level (SOr  _ _) = 5
level (SImp _ _) = 2

lp :: forall (a :: Formula) (b :: Formula). (Seqt a, Seqt b) =>
      (Int -> Int -> Bool) -> Sing a -> Sing b -> String
lp f x e = (if f (level x) (level e) then parens else id) (ppt x)

parens :: String -> String
parens s = "(" ++ s ++ ")"

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

-------------------------------------------------------------------------------
               -- Basic Data Types and Data Kinds
-------------------------------------------------------------------------------

-- Three variables are enough for most theorems,
-- we can always add more here if we need.
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

-- Some alias type operators for convenience and readability.
type (/\) = And
type (\/) = Or
type (~>) = Imp

type VA = Var A
type VB = Var B
type VC = Var C

-------------------------------------------------------------------------------
                -- Sequent type class for printing
-------------------------------------------------------------------------------

-- `ppt` takes the data of a singleton type and prints it,
-- the inhabitant of the singleton type will be given by `sing` method
-- provided by the singletons library.
class SingI gamma => Seqt (gamma :: k) where
  ppt :: Sing gamma -> String

instance Seqt (Var A) where
  ppt _ = "A"

instance Seqt (Var B) where
  ppt _ = "B"

instance Seqt (Var C) where
  ppt _ = "C"

instance Seqt Top where
  ppt _ = "True"

instance Seqt Bottom where
  ppt _ = "False"

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

-- For associations, etc.
level :: forall (a :: Formula). Seqt a => Sing a -> Int
level (SVar _)   = 100
level STop       = 100
level SBottom    = 100
level (SNot _)   = 10
level (SAnd _ _) = 8
level (SOr  _ _) = 5
level (SImp _ _) = 2

-- A generic function to decide if some parenthesis need to be put\
-- around some string.
lp :: forall (a :: Formula) (b :: Formula). (Seqt a, Seqt b) =>
      (Int -> Int -> Bool) -> Sing a -> Sing b -> String
lp f x e = (if f (level x) (level e) then parens else id) (ppt x)

parens :: String -> String
parens s = "(" ++ s ++ ")"

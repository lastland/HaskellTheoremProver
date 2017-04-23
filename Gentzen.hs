{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE KindSignatures    #-}
{-# LANGUAGE PolyKinds         #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeFamilies      #-}

module Gentzen where

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
  ppt (SNot a@(SVar _)) = "~" ++ ppt a
  ppt (SNot a)          = "~(" ++ ppt a ++ ")"

instance (Seqt a, Seqt b) => Seqt (And a b) where
  ppt (SAnd a b@(SVar _)) = ppt a ++ " /\\ " ++ ppt b
  ppt (SAnd a STop) = ppt a ++ " /\\ " ++ ppt STop
  ppt (SAnd a SBottom) = ppt a ++ " /\\ " ++ ppt SBottom
  ppt (SAnd a b) = ppt a ++ " /\\ (" ++ ppt b ++ ")"

instance (Seqt a, Seqt b) => Seqt (Or a b) where
  ppt (SOr a b@(SVar _)) = ppt a ++ " \\/ " ++ ppt b
  ppt (SOr a STop) = ppt a ++ " \\/ " ++ ppt STop
  ppt (SOr a SBottom) = ppt a ++ " \\/ " ++ ppt SBottom
  ppt (SOr a b) = ppt a ++ " \\/ (" ++ ppt b ++ ")"

instance (Seqt a, Seqt b) => Seqt (Imp a b) where
  ppt (SImp a b) = ppt a ++ " -> " ++ ppt b

instance Seqt ('[]) where
  ppt (S.SNil)       = ""

instance (Seqt a, Seqt as) => Seqt (a ': as) where
  ppt (S.SCons a S.SNil) = ppt a
  ppt (S.SCons a as)     = (ppt a) ++ ", " ++ (ppt as)

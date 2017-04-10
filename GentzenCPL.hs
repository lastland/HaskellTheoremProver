{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE KindSignatures     #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies       #-}
{-# LANGUAGE TypeOperators      #-}

module CPL where

import           Control.Monad

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

type family (:++:) (a :: [Formula]) (b :: [Formula]) :: [Formula] where
  '[] :++: x = x
  '[x] :++: y = (x:y)
  (x:xs) :++: y = x:(xs :++: y)

data Derives :: [Formula] -> [Formula] -> * where
  I      :: Derives '[a] '[a]
  Cut    :: Derives gamma (a:delta) ->
            Derives (a:sigma) pi ->
            Derives (gamma :++: sigma) (delta :++: pi)
  LConj1 :: Derives (a:gamma) delta ->
            Derives ((And a b):gamma) delta
  LConj2 :: Derives (b:gamma) delta ->
            Derives ((And a b):gamma) delta
  LDisj  :: Derives (a:gamma) delta ->
            Derives (b:sigma) pi ->
            Derives ((Or a b):(gamma :++: sigma)) (delta :++: pi)
  LImp   :: Derives (gamma) (a:delta) ->
            Derives (b:sigma) pi ->
            Derives ((Imp a b):(gamma :++: sigma)) (delta :++: pi)
  LNot   :: Derives gamma delta ->
            Derives ((Not a):gamma) delta
  RDisj1 :: Derives gamma (a:delta) ->
            Derives gamma ((Or a b):delta)
  RDisj2 :: Derives gamma (b:delta) ->
            Derives gamma ((Or a b):delta)
  RConj  :: Derives gamma (a:delta) ->
            Derives sigma (b:pi) ->
            Derives (gamma :++: sigma) ((And a b):(delta :++: pi))
  RImp   :: Derives (a:gamma) (b:delta) ->
            Derives gamma ((Imp a b):delta)
  RNot   :: Derives (a:gamma) delta ->
            Derives gamma ((Not a):delta)
  LW     :: Derives gamma delta ->
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
deriving instance Show (Derives a b)

type Sequent = ([Formula], [Formula])

tryRule :: (Sequent -> Sequent) -> String -> Sequent -> IO Sequent
tryRule rule name sq = do
  let sq' = rule sq
      output = (show (fst sq')) ++ " |- " ++ (show (snd sq'))
  replicateM (length output + 1) (putStr "-")
  putStrLn $ " " ++ name
  putStrLn output
  return sq'

tryI :: Formula -> IO Sequent
tryI a = tryRule id "I" ([a], [a])

tryRNot :: Sequent -> IO Sequent
tryRNot = tryRule f "RNot" where
  f (a:g, d) = (g, (Not a):d)
  f sq       = sq

tryRDisj1 :: Formula -> Sequent -> IO Sequent
tryRDisj1 b = tryRule f "RDisj1" where
  f (g, a:d) = (g, (Or a b):d)
  f sq       = sq

tryRDisj2 :: Formula -> Sequent -> IO Sequent
tryRDisj2 a = tryRule f "RDisj2" where
  f (g, b:d) = (g, (Or a b):d)
  f sq       = sq

tryPR :: Sequent -> IO Sequent
tryPR = tryRule f "PR" where
  f (g, a:b:d) = (g, b:a:d)
  f sq         = sq

tryCR :: Sequent -> IO Sequent
tryCR = tryRule f "CR" where
  f (g, a:b:d) | a == b = (g, a:d)
               | otherwise = (g, a:b:d)
  f sq         = sq

tryDerive :: IO ()
tryDerive = tryI (Var A) >>=
            tryRNot >>=
            tryRDisj2 (Var A) >>=
            tryPR >>=
            tryRDisj1 (Not (Var A)) >>=
            tryCR >>
            return ()

simple :: Derives '[Var A] '[Var A]
simple = I

excludedMiddle :: Derives '[] '[Or (Var A) (Not (Var A))]
excludedMiddle = CR . RDisj1 . PR . RDisj2 . RNot $ I

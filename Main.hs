import           Control.Monad
import           Data.Maybe
import           System.IO
import           Test.HUnit
import           Text.Read

import qualified FmlKind.Basic              as KGBasic
import qualified FmlKind.GentzenCPL         as KGCl
import qualified FmlKind.GentzenCPLTheorems as KGClTheorems
import qualified FmlKind.GentzenIPL         as KGInt
import qualified FmlKind.GentzenIPLTheorems as KGIntTheorems
import qualified FmlTypeConstr.Basic        as TCBasic
import qualified FmlTypeConstr.GStyleCl     as TCGCl
import qualified FmlTypeConstr.GStyleInt    as TCGInt
import qualified FmlTypeConstr.NDedCl       as TCNDedCl
import qualified FmlTypeConstr.NDedInt      as TCNDedInt
import qualified FmlTypeConstr.ProofObjects as TCProofObjects
import qualified FmlTypeConstr.Provability  as TCProvability
import qualified FunImpl.NDed               as FNDed
import qualified FunImpl.NDedTests          as FNDedTests
import qualified FunImpl.NDedTheorems       as FNDedTheorems
import           Printing.Proof             (getTree)
import qualified Printing.Proof             as Proof
import           Printing.ProofTree         (ProofTree, printTree, showTheorem)
import qualified Printing.ProofTree         as ProofTree


-- Run tests, then enter the main menu.
main :: IO ()
main = do
  putStrLn "Welcome to our Theorem Prover!"
  putStrLn "Let's start by running some tests:"
  putStrLn "Some Intuitionistic Theorems"
  runTestTT FNDedTests.testInt
  putStrLn "Some Classical Theorems"
  runTestTT FNDedTests.testCl
  putStrLn "Tests completed."
  mainMenu
  putStrLn "Bye!"

-------------------------------------------------------------------------------
                   -- Theorems and Proofs to Show
-------------------------------------------------------------------------------

data Logic = Classic | Intuition

instance Show Logic where
  show Classic   = "classical logic"
  show Intuition = "intuitionistic logic"

-- Data-level theorems with natural deduction style proofs.
nDedProofs :: [(ProofTree, Logic)]
nDedProofs = mapMaybe (\(x, y) -> flip (,) y <$> getTree x)
             [(FNDedTheorems.andFlip a b, Intuition),
              (FNDedTheorems.orFlip a b, Intuition),
              (FNDedTheorems.distr1 a b c, Intuition),
              (FNDedTheorems.distr2 a b c, Intuition),
              (FNDedTheorems.deMorgOr a b, Intuition),
              (FNDedTheorems.impOr a b, Intuition),
              (FNDedTheorems.tranApp a b c, Intuition),
              (FNDedTheorems.doubNegImp a, Intuition),
              (FNDedTheorems.wkPeirce a b, Intuition),
              (FNDedTheorems.lem a, Classic),
              (FNDedTheorems.doubNegElim a, Classic),
              (FNDedTheorems.deMorgAnd a b, Classic),
              (FNDedTheorems.orImp a b, Classic),
              (FNDedTheorems.peirceL a b, Classic)] where
  a = FNDed.Var 'A'
  b = FNDed.Var 'B'
  c = FNDed.Var 'C'

-- Type-level theorems with Gentzen-style proofs.
-- Notice: We can't use `map KGInt.pp ...` here,
-- because all theorems have different types!
gentzenProofs :: [(ProofTree, Logic)]
gentzenProofs = [(KGInt.pp KGIntTheorems.notTandF', Intuition),
                 (KGInt.pp KGIntTheorems.andFlip', Intuition),
                 (KGInt.pp KGIntTheorems.orFlip', Intuition),
                 (KGInt.pp KGIntTheorems.distr1', Intuition),
                 (KGInt.pp KGIntTheorems.distr2', Intuition),
                 (KGInt.pp KGIntTheorems.impTrans', Intuition),
                 (KGInt.pp KGIntTheorems.doubleNegImp', Intuition),
                 (KGInt.pp KGIntTheorems.deMorgan1', Intuition),
                 (KGInt.pp KGIntTheorems.deMorgan2', Intuition),
                 (KGCl.pp KGClTheorems.doubNeg1', Classic),
                 (KGCl.pp KGClTheorems.excludedMiddle', Classic)]

-------------------------------------------------------------------------------
                     -- All the Menus
-------------------------------------------------------------------------------

-- The main menu.
mainMenu :: IO ()
mainMenu = do
  putSeparation "="
  putStrLn "What would you like me to do?"
  putStrLn "1: Print some proofs in natural deductions."
  putStrLn "   (Propositions are implemented at data level in this version)"
  putStrLn "2: Print some proofs in Gentzen style."
  putStrLn "   (Propositions are implemented at type level in this version)"
  putStrLn "x: Exit."
  putStr "Please enter your command (1, 2, or x): "
  hFlush stdout
  c <- getLine
  runCommandMainMenu c


-- Execute user's command in the main menu.
runCommandMainMenu :: String -> IO ()
runCommandMainMenu "1" = showProofMenu nDedProofs
runCommandMainMenu "2" = showProofMenu gentzenProofs
runCommandMainMenu "x" = return ()
runCommandMainMenu _ = do
  putStrLn "Sorry. I don't understand your command. Please try again."
  mainMenu


-- The "show proof menu":
-- Users can choose to print the proof of a theorem from our theorem list,
-- or get back to the main menu, or exit our program.
-- Notice that this function is shared by
-- the part that prints data-level theorems with proofs
-- in natural deduction styles,
-- and the part that prints type-level theorems with proofs
-- in Gentzen style.
showProofMenu :: [(ProofTree, Logic)] -> IO ()
showProofMenu pfs = do
  putSeparation "-"
  putStrLn "Which proof would you like me to print?"
  mapM_ putStrLn (theoremsToShow pfs)
  putStrLn "q: get back to previous menu."
  putStrLn "x: Exit."
  putStr "Please enter your command: "
  hFlush stdout
  c <- getLine
  runCommandShowProofMenu pfs c


-- Execute the command in the show proof menu.
-- Print the `ProofTree` if the command is a valid number.
runCommandShowProofMenu :: [(ProofTree, Logic)] -> String -> IO ()
runCommandShowProofMenu _ "x" = return ()
runCommandShowProofMenu _ "q" = mainMenu
runCommandShowProofMenu pfs x =
  (case (readMaybe x :: Maybe Int) of
    Just i ->
      if i <= length pfs then
        printTree $ fst (pfs !! (i - 1))
        else putStrLn "Invalid number."
    Nothing ->
      putStrLn $ "Sorry. I don't understand your command." ++
      " Please try again.") >>
 showProofMenu pfs


-- Takes a list of `ProofTree``, show the proved theorems
theoremsToShow :: [(ProofTree, Logic)] -> [String]
theoremsToShow ps = [show i ++ ": " ++ showTheorem t ++
                      " (" ++ show l ++ ")" |
                      (i, (t, l)) <- zip [1..] ps]

-- Put some separation symbols on the screen
putSeparation :: String -> IO ()
putSeparation c = replicateM_ 80 (putStr c) >> putStrLn ""

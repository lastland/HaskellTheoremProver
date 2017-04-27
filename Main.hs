import           Control.Monad
import           Data.Maybe
import           System.IO
import           Test.HUnit
import           Text.Read

import qualified FmlKind.Gentzen            as KGentzen
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


nDedProofs :: [ProofTree]
nDedProofs = mapMaybe getTree
             [FNDedTheorems.andFlip a b,
              FNDedTheorems.orFlip a b,
              FNDedTheorems.distr1 a b c,
              FNDedTheorems.distr2 a b c,
              FNDedTheorems.deMorgOr a b,
              FNDedTheorems.impOr a b,
              FNDedTheorems.tranApp a b c,
              FNDedTheorems.doubNegImp a,
              FNDedTheorems.wkPeirce a b,
              FNDedTheorems.lem a,
              FNDedTheorems.doubNegElim a,
              FNDedTheorems.deMorgAnd a b,
              FNDedTheorems.orImp a b,
              FNDedTheorems.peirceL a b] where
  a = FNDed.Var 'A'
  b = FNDed.Var 'B'
  c = FNDed.Var 'C'

-- Can we use `map KGInt.pp ...` here?
-- No, because all theorems have different types!
gentzenProofs :: [ProofTree]
gentzenProofs = [KGInt.pp KGIntTheorems.notTandF',
                 KGInt.pp KGIntTheorems.andFlip',
                 KGInt.pp KGIntTheorems.orFlip',
                 KGInt.pp KGIntTheorems.distr1',
                 KGInt.pp KGIntTheorems.distr2',
                 KGInt.pp KGIntTheorems.impTrans',
                 KGInt.pp KGIntTheorems.doubleNegImp',
                 KGInt.pp KGIntTheorems.deMorgan1',
                 KGInt.pp KGIntTheorems.deMorgan2']

main :: IO ()
main = do
  putStrLn "Welcome to our Theorem Prover!"
  putStrLn "Let's start by running some tests:"
  runTestTT FNDedTests.testInt
  runTestTT FNDedTests.testInt
  putStrLn "Tests completed."
  mainMenu
  putStrLn "Bye!"
  where
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
    runCommandMainMenu :: String -> IO ()
    runCommandMainMenu "1" = showProofMenu nDedProofs
    runCommandMainMenu "2" = showProofMenu gentzenProofs
    runCommandMainMenu "x" = return ()
    runCommandMainMenu _ = do
      putStrLn "Sorry. I don't understand your command. Please try again."
      mainMenu
    showProofMenu :: [ProofTree] -> IO ()
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
    runCommandShowProofMenu :: [ProofTree] -> String -> IO ()
    runCommandShowProofMenu _ "x" = return ()
    runCommandShowProofMenu _ "q" = mainMenu
    runCommandShowProofMenu pfs x =
      (case (readMaybe x :: Maybe Int) of
        Just i ->
          if i <= length pfs then
            printTree (pfs !! (i - 1))
            else putStrLn "Invalid number."
        Nothing ->
          putStrLn $ "Sorry. I don't understand your command." ++
          " Please try again.") >>
     showProofMenu pfs
    theoremsToShow :: [ProofTree] -> [String]
    theoremsToShow ps = [show i ++ ": " ++ showTheorem t |
                          (i, t) <- zip [1..] ps]
    putSeparation :: String -> IO ()
    putSeparation c = replicateM_ 80 (putStr c) >> putStrLn ""

module FunImpl.NDedTests where

import           FunImpl.NDed
import           FunImpl.NDedTheorems
import           Printing.Proof
import           Printing.ProofTree
import           Test.HUnit

---------------------------------------------------------------------------
        --Tests
---------------------------------------------------------------------------

testInt :: Test
testInt = "Intuitionistic Theorems" ~:
        TestList [printT (andFlip (Var 'a') (Var 'b')) ~?=
                   "a /\\ b |- b /\\ a",
                  printT (orFlip (Var 'a') (Var 'b')) ~?=
                   "a \\/ b |- b \\/ a",
                  printT (distr1 (Var 'a') (Var 'b') (Var 'c')) ~?=
                   "a /\\ (b \\/ c) |- a /\\ b \\/ a /\\ c",
                  printT (distr2 (Var 'a') (Var 'b') (Var 'c')) ~?=
                   "a \\/ b /\\ c |- (a \\/ b) /\\ (a \\/ c)",
                  printT (deMorgOr (Var 'a') (Var 'b')) ~?=
                   "~(a \\/ b) |- ~a /\\ ~b",
                  printT (tranApp (Var 'a') (Var 'b') (Var 'c'))
                        ~?= "a, a ~> b, a ~> b ~> c |- c",
                  printT (impOr (Var 'a') (Var 'b'))
                        ~?= "~a \\/ b |- a ~> b",
                  printT (wkPeirce (Var 'a') (Var 'b'))
                        ~?= "|- ((((a ~> b) ~> a) ~> a) ~> b) ~> b"
                ]
           where printT = showMaybeTheorem . getTree

testCl :: Test
testCl = "Classical Theorems" ~:
       TestList [ printT (lem (Var 'a')) ~?= "|- a \\/ ~a",
                  printT (doubNegElim (Var 'a')) ~?= "~(~a) |- a",
                  printT (deMorgAnd (Var 'a') (Var 'b'))
                       ~?= "~(a /\\ b) |- ~a \\/ ~b",
                  printT (orImp (Var 'a') (Var 'b'))
                       ~?= "a ~> b |- ~a \\/ b",
                  printT (peirceL (Var 'a') (Var 'b'))
                       ~?= "|- ((a ~> b) ~> a) ~> a"]
         where printT = showMaybeTheorem . getTree

--------------------------------------------------------------------------

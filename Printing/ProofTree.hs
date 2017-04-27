module Printing.ProofTree where

import           Data.Tree
import           Data.Tree.Pretty

type ProofTree = Tree String

pNode = Node

showTree :: ProofTree -> String
showTree = drawVerticalTreeWith 5

showMaybeTree :: Maybe ProofTree -> String
showMaybeTree (Just t) = showTree t
showMaybeTree _        = "The proof was wrong"

printTree :: ProofTree -> IO ()
printTree = putStrLn . showTree

printMaybeTree :: Maybe ProofTree -> IO ()
printMaybeTree = putStrLn . showMaybeTree

showTheorem :: ProofTree -> String
showTheorem (Node thm _) = thm

showMaybeTheorem :: Maybe ProofTree -> String
showMaybeTheorem (Just t) = showTheorem t
showMaybeTheorem _        = "No proven theorem"

printTheorem :: ProofTree -> IO ()
printTheorem = putStrLn . showTheorem

printMaybeTheorem :: Maybe ProofTree -> IO ()
printMaybeTheorem = putStrLn . showMaybeTheorem

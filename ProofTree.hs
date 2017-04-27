module ProofTree where

import           Data.Tree
import           Data.Tree.Pretty

type ProofTree = Tree String

pNode = Node

printTree :: ProofTree -> IO ()
printTree = putStrLn . drawVerticalTreeWith 5

printMaybeTree :: Maybe ProofTree -> IO ()
printMaybeTree (Just t) = printTree t
printMaybeTree _        = putStrLn "The proof was wrong"

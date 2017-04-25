module ProofTree where

import           Data.Tree
import           Data.Tree.Pretty

type ProofTree = Tree String

pNode = Node

printTree :: ProofTree -> IO ()
printTree = putStrLn . drawVerticalTreeWith 5

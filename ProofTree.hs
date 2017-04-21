module ProofTree where

import           Data.Tree
import           Data.Tree.Pretty

type ProofTree = Tree String

pNode = Node

printTree :: ProofTree -> String
printTree = drawVerticalTreeWith 5

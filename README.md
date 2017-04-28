# Theorem Proving in Haskell

This is an overview of a theorem proving project in Haskell, carried out by
Pritam Choudhury (pritam) and Yao Li (liyao) as part of the coursework for
CIS 552.

## Prerequisite

The following libraries are needed for running the programs.

    cabal install pretty-tree
    cabal install singletons

## Introduction

This project develops a theorem proving framework for intuitionistic and
classical propositional logics in Haskell. For formalising these logics, we used
the sequent style approach, meaning the theorems are sequents where the
antecedent of the sequent is the list of hypotheses and the succedent of the
sequent is the thesis. There are two well-known methods that formalises logical
theorems as sequents. One of them is the Natural Deduction style, the other is
the Gentzen style. We implemented both of them.

For formalising in either style, we first need to encode the rules of inference.
The rules of inference can be encoded as _partial functions_ on sequents or as
_constructors of an inductive data structure_.

## Function Implementation

The implementation using functions is carried out in `FunImpl`. This folder has
three files:
- The file `NDed.hs` contains the rules of inference represented as partial
  functions.
- The file `NDedTheorems.hs` contains some theorems proved using the functions
  exported from `NDed.hs`.
- The file `NDedTests.hs` contains unit tests checking the output of the
  functions (representing theorems) developed in `NDedTheorems.hs`.

## Type-Level Implementation

The functional implementation is a bit verbose and less expressive. We can
overcome these problems by encoding the rules of inference as constructors of an
inductive data structure. We explore two ways in which this can be acheived.

### Formula as Kind

In the first approach, we construct a new kind, `Formula`, the type of all
formulas. With this, we can construct an inductive data structure that contains
all the rules of inference. So the language is now more expressive and the
theorems are shorter.

This is implemented in `FmlKind`. This folder has five files:
- The file `Basic.hs` contains the basic definitions for this approach.
- The file `GentzenCPL.hs` contains the Gentzen style rules for classical
  propositional logic.
- The file `GentzenCPLTheorems.hs` contains some theorems proved using the rules
  specified in `GentzenCPL.hs`.
- The file `GentzenIPL.hs` contains the Gentzen style rules for intuitionistic
  propositional logic.
- The file `GentzenIPLTheorems.hs` contains some theorems proved using the rules
  specified in `GentzenIPL.hs`.

#### Printing

To support printing for the proof-trees we generate, we have `Printing`.
`FunImpl` and `FmlKind` use this folder. This folder contains two files:
- The file `ProofTree.hs` builds upon the `pretty-tree` printing library for
  printing the proof trees.
- The file `Proof.hs` defines some higher-order functions that transform rules
  of inference into combinators for proof-trees.

### Formula as Type Constructors

In the Formula as Kind approach, we can't populate the individual formulas with
terms. So we explore a second approach that enables us to do so. In this
approach, `Formula` is a type constructor of kind `* -> *` . The individual
formulas are Haskell types and as such, we can populate them with terms. So
we can have derivation (using just the rules of inference) and evidence (by
looking inside the types or formulas) in the same setting.

This is implemented in `FmlTypeConstr`. This folder has seven files:
- The file `Basic.hs` contains the basic definitions for this approach.
- The file `NDedInt.hs` and `NDedCl.hs` contain the natural deduction style
  rules for intuitionistic propositional logic and classical propositional logic
  respectively, along with some example theorems.
- The file `GStyleInt.hs` and `GStyleCl.hs` contain the Gentzen style rules for
  intuitionistic propositional logic and classical propositional logic
  respectively, along with some example theorems.
- The file `ProofObjects.hs` contains the intuitionistic natural deduction rules
  along with the corresponding proof-objects and some example theorems.
- The file `Provability.hs` deals with evidence based proving of intuitionistic
  theorems.

## Main.hs

The `Main.hs` file implements an interactive program that shows some sample
results.

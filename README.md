                                  Theorem Proving in Haskell
                                ------------------------------
                                
This is an overview of a theorem proving project in Haskell, carried out by Pritam Choudhury (pritam) and Yao Li (liyao) as part of the coursework for CIS 552. The following libraries are needed for running the programs. 

[pretty-tree](https://hackage.haskell.org/package/pretty-tree)

[singletons](https://hackage.haskell.org/package/singletons)

This project develops a theorem proving framework for intuitionistic and classical propositional logics in Haskell. For formalising these logics, we used the sequent style approach, meaning the theorems are sequents where the antecedent of the sequent is the list of hypotheses and the succedent of the sequent is the thesis. There are two well-known methods that formalises logical theorems as sequents. One of them is the Natural Deduction style, the other is the Gentzen style. We implemented both of them.

For formalising in either style, we first need to encode the rules of inference. The rules of inference can be encoded as partial functions on sequents or as constructors of an inductive data structure. 

The implementation using functions is carried out in FunImpl. This folder has three files. The file NDed.hs contains the rules of inference represented as partial functions. The file NDedTheorems.hs contains some theorems proved using the functions exported from NDed.hs. The file NDedTests.hs contains unit tests checking the output of the functions (representing theorems) developed in NDedTheorems.hs.

The functional implementation is a bit verbose and less expressive. We can overcome these problems by encoding the rules of inference as constructors of an inductive data structure. We explore two ways in which this can be acheived.

In the first approach, we construct a new kind, Formula, the type of all formulas. With this, we can construct an inductive data structure that contains all the rules of inference. So the language is now more expressive and the theorems are shorter. This implementation is carried out in FmlKind. This folder has five files. The file ---- contains the basic definitions for this approach. The file GentzenCPL.hs contains the Gentzen style rules for classical propositional logic. The file GentzenCPLTheorems.hs contains some theorems proved using the rules specified in GentzenCPL.hs.   

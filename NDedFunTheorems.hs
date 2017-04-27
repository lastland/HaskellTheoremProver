{-# LANGUAGE FlexibleInstances #-}

module NDedFunTheorems where

import           Data.Set   hiding (map)
import           NDedFun
import           Proof
import           ProofTree
import           Test.HUnit

------------------------------------------------------------------------
        --Intuitionistic Theorems
------------------------------------------------------------------------

-- p /\ q |- q /\ p (Int)
andFlip :: Formula -> Formula -> Pf
andFlip p q = let init = axP (p /\ q) (singleton (p /\ q))
                  s1 = andEP2 init
                  s2 = andEP1 init in
                  andIP s1 s2

-- p \/ q |- q \/ p (Int)
orFlip :: Formula -> Formula -> Pf
orFlip p q = let hyp = singleton (p \/ q)
                 s1 = axP p (insert p hyp)
                 s2 = axP q (insert q hyp)
                 s3 = orIP2 q s1
                 s4 = orIP1 p s2
                 s5 = axP (p \/ q) hyp in
               orEP s3 s4 s5

-- p /\ (q \/ r) |- (p /\ q) \/ (p /\ r) (Int)
distr1 :: Formula -> Formula -> Formula -> Pf
distr1 p q r = let hyp  = (p /\ (q \/ r))
                   hyp1 = insert q (singleton hyp)
                   hyp2 = insert r (singleton hyp)
                   s0 = axP hyp (singleton hyp)
                   s1 = axP hyp hyp1
                   s2 = axP hyp hyp2
                   s3 = axP q hyp1
                   s4 = axP r hyp2
                   s5 = andEP1 s1
                   s6 = andEP1 s2
                   s7 = andIP s5 s3
                   s8 = andIP s6 s4
                   s9 = andEP2 s0
                   s10 = orIP1 (p /\ r) s7
                   s11 = orIP2 (p /\ q) s8 in
                 orEP s10 s11 s9

-- p \/ (q /\ r) |- (p \/ q) /\ (p \/ r) (Int)
distr2 :: Formula -> Formula -> Formula -> Pf
distr2 p q r = let hyp  = (p \/ (q /\ r))
                   hyp1 = insert p (singleton hyp)
                   hyp2 = insert (q /\ r) (singleton hyp)
                   s0 = axP hyp (singleton hyp)
                   s1 = axP p hyp1
                   s2 = orIP1 q s1
                   s3 = orIP1 r s1
                   s4 = andIP s2 s3
                   s5 = axP (q /\ r) hyp2
                   s6 = andEP1 s5
                   s7 = andEP2 s5
                   s8 = orIP2 p s6
                   s9 = orIP2 p s7
                   s10 = andIP s8 s9 in
                 orEP s4 s10 s0

-- ~(p \/ q) |- ~p /\ ~q (Int)
deMorgOr :: Formula -> Formula -> Pf
deMorgOr p q = let hyp  = ((p \/ q) ~> Bot)
                   hyp1 = insert p (singleton hyp)
                   hyp2 = insert q (singleton hyp)
                   s0 = axP hyp hyp1
                   s1 = axP hyp hyp2
                   s2 = axP p hyp1
                   s3 = axP q hyp2
                   s4 = orIP1 q s2
                   s5 = orIP2 p s3
                   s6 = impEP s0 s4
                   s7 = impIP p s6
                   s8 = impEP s1 s5
                   s9 = impIP q s8 in
                 andIP s7 s9

-- p -> q |- ~p \/ q (Int)
impOr :: Formula -> Formula -> Pf
impOr p q = let hyp  = insert p (singleton ((p ~> Bot) \/ q))
                hyp1 = insert (p ~> Bot) hyp
                hyp2 = insert q hyp
                s0 = axP ((p ~> Bot) \/ q) hyp
                s1 = axP p hyp1
                s2 = axP (p ~> Bot) hyp1
                s3 = impEP s2 s1
                s4 = botEIntP q s3
                s5 = axP q hyp2
                s6 = orEP s4 s5 s0 in
                impIP p s6

-- p -> (q -> r), p -> q, p |- r (Int)
tranApp :: Formula -> Formula -> Formula -> Pf
tranApp p q r = let
     hyp = insert (p ~> (q ~> r)) ((insert (p ~> q)) (singleton p))
     s1 = axP (p ~> (q ~> r)) hyp
     s2 = axP p hyp
     s3 = impEP s1 s2
     s4 = axP (p ~> q) hyp
     s5 = impEP s4 s2 in
  impEP s3 s5

-- p |- ~~p (Int)
doubNegImp :: Formula -> Pf
doubNegImp p = let hyp = insert (p ~> Bot) (singleton p)
                   s1 = axP (p ~> Bot) hyp
                   s2 = axP p hyp
                   s3 = impEP s1 s2 in
                 impIP (p ~> Bot) s3

-- |- ((((p -> q) -> p) -> p) -> q) -> q (Int)
wkPeirce :: Formula -> Formula -> Pf
wkPeirce p q = let fm1 = (((p ~> q) ~> p) ~> p) ~> q
                   fm2 = (p ~> q) ~> p
                   hyp1 = insert fm2 (singleton fm1)
                   hyp2 = insert p hyp1
                   s0 = axP p hyp2
                   s1 = impIP fm2 s0
                   s2 = wknP fm2 s1
                   s3 = axP fm1 hyp2
                   s4 = impEP s3 s2
                   s5 = impIP p s4
                   s6 = axP fm2 hyp1
                   s7 = impEP s6 s5
                   s8 = impIP fm2 s7
                   s9 = axP fm1 (singleton fm1)
                   s10 = impEP s9 s8 in
                 impIP fm1 s10

--------------------------------------------------------------------------
        --Classical Theorems
--------------------------------------------------------------------------

-- |- p \/ ~p (Cl)
lem :: Formula -> Pf
lem p = let s0 = deMorgOr p (p ~> Bot)
            s1 = andEP2 s0
            s2 = andEP1 s0
            s3 = impEP s1 s2 in
    botEClP (p \/ (p ~> Bot)) s3

-- ~~p |- p (Cl)
doubNegElim :: Formula -> Pf
doubNegElim p = let fm1 = p ~> Bot
                    fm2 = fm1 ~> Bot
                    hyp = insert fm1 (singleton fm2)
                    s0 = axP fm2 hyp
                    s1 = axP fm1 hyp
                    s2 = impEP s0 s1 in
                  botEClP p s2

-- ~(p /\ q) |- ~p \/ ~q (Cl)
deMorgAnd p q = let fm1 = (p /\ q) ~> Bot
                    hyp1 = insert q (singleton fm1)
                    hyp2 = insert p hyp1
                    hyp3 = insert (q ~> Bot) (singleton fm1)
                    s0 = lem q
                    s1 = wknP fm1 s0
                    s2 = axP p hyp2
                    s3 = axP q hyp2
                    s4 = andIP s2 s3
                    s5 = axP fm1 hyp2
                    s6 = impEP s5 s4
                    s7 = impIP p s6
                    s8 = orIP1 (q ~> Bot) s7
                    s9 = axP (q ~> Bot) hyp3
                    s10 = orIP2 (p ~> Bot) s9 in
                  orEP s8 s10 s1

-- ~p \/ q |- p -> q (Cl)
orImp :: Formula -> Formula -> Pf
orImp p q = let fm = p ~> q
                hyp1 = insert p (singleton fm)
                hyp2 = insert (p ~> Bot) (singleton fm)
                s0 = lem p
                s1 = wknP fm s0
                s2 = axP fm hyp1
                s3 = axP p hyp1
                s4 = impEP s2 s3
                s5 = orIP2 (p ~> Bot) s4
                s6 = axP (p ~> Bot) hyp2
                s7 = orIP1 q s6 in
              orEP s5 s7 s1

-- |- (((p -> q) -> p) -> p) -> q (Cl)
peirceL :: Formula -> Formula -> Pf
peirceL p q = let fm = (p ~> q) ~> p
                  hyp1 = insert (p ~> Bot) (singleton fm)
                  hyp2 = insert p hyp1
                  s0 = axP (p ~> Bot) hyp2
                  s1 = axP p hyp2
                  s2 = impEP s0 s1
                  s3 = wknP (q ~> Bot) s2
                  s4 = botEClP q s3
                  s5 = impIP p s4
                  s6 = axP fm hyp1
                  s7 = impEP s6 s5
                  s8 = axP p (insert p (singleton fm))
                  s9 = lem p
                  s10 = wknP fm s9
                  s11 = orEP s8 s7 s10 in
                impIP fm s11

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

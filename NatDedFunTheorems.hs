{-# LANGUAGE FlexibleInstances #-}

module NatDedFunTheorems where

import           Data.Set         hiding (map)
import           NatDedFun
import           Test.HUnit
import           Text.PrettyPrint

------------------------------------------------------------------------
        --Intuitionistic Theorems
------------------------------------------------------------------------

-- p /\ q |- q /\ p (Int)
andFlip :: Formula -> Formula -> Maybe Sequent
andFlip p q = do
         init <- ax (p /\ q) (singleton (p /\ q))
         s1 <- andE2 init
         s2 <- andE1 init
         andI s1 s2

-- p /\ q |- q /\ p (Int)
andFlip' :: Formula -> Formula -> Pf
andFlip' p q = let init = axP (p /\ q) (singleton (p /\ q))
                   s1 = andEP2 init
                   s2 = andEP1 init in
                   andIP s1 s2

-- p \/ q |- q \/ p (Int)
orFlip :: Formula -> Formula -> Maybe Sequent
orFlip p q = let hyp = singleton (p \/ q) in do
       s1 <- ax p (insert p hyp)
       s2 <- ax q (insert q hyp)
       s3 <- orI2 q s1
       s4 <- orI1 p s2
       s5 <- ax (p \/ q) hyp
       orE s3 s4 s5

-- p \/ q |- q \/ p (Int)
orFlip' :: Formula -> Formula -> Pf
orFlip' p q = let hyp = singleton (p \/ q)
                  s1 = axP p (insert p hyp)
                  s2 = axP q (insert q hyp)
                  s3 = orIP2 q s1
                  s4 = orIP1 p s2
                  s5 = axP (p \/ q) hyp in
                orEP s3 s4 s5

-- p /\ (q \/ r) |- (p /\ q) \/ (p /\ r) (Int)
distr1 :: Formula -> Formula -> Formula -> Maybe Sequent
distr1 p q r = let hyp  = (p /\ (q \/ r))
                   hyp1 = insert q (singleton hyp)
                   hyp2 = insert r (singleton hyp) in do
            s0 <- ax hyp (singleton hyp)
            s1 <- ax hyp hyp1
            s2 <- ax hyp hyp2
            s3 <- ax q hyp1
            s4 <- ax r hyp2
            s5 <- andE1 s1
            s6 <- andE1 s2
            s7 <- andI s5 s3
            s8 <- andI s6 s4
            s9 <- andE2 s0
            s10 <- orI1 (p /\ r) s7
            s11 <- orI2 (p /\ q) s8
            orE s10 s11 s9

-- p \/ (q /\ r) |- (p \/ q) /\ (p \/ r) (Int)
distr2 :: Formula -> Formula -> Formula -> Maybe Sequent
distr2 p q r = undefined

-- (p /\ q) \/ (p /\ r) |- p /\ (q \/ r) (Int)
distr'1 :: Formula -> Formula -> Formula -> Maybe Sequent
distr'1 p q r = undefined

-- (p \/ q) /\ (p \/ r) |- p \/ (q /\ r) (Int)
distr'2 :: Formula -> Formula -> Formula -> Maybe Sequent
distr'2 = undefined

-- ~(p \/ q) |- ~p /\ ~q (Int)
deMorgOr :: Formula -> Formula -> Maybe Sequent
deMorgOr p q = undefined

-- ~p /\ ~q |- ~(p \/ q) (Int)
deMorgOr' :: Formula -> Formula -> Maybe Sequent
deMorgOr' p q = undefined

-- p -> q |- ~p \/ q (Int)
impOr :: Formula -> Formula -> Maybe Sequent
impOr p q = undefined

-- p -> (q -> r), p -> q, p |- r (Int)
tranApp :: Formula -> Formula -> Formula -> Maybe Sequent
tranApp p q r = let
     hyp = insert (p ~> (q ~> r)) ((insert (p ~> q)) (singleton p)) in do
       s1 <- ax (p ~> (q ~> r)) hyp
       s2 <- ax p hyp
       s3 <- impE s1 s2
       s4 <- ax (p ~> q) hyp
       s5 <- impE s4 s2
       impE s3 s5

-- p |- ~~p (Int)
doubNegImp :: Formula -> Maybe Sequent
doubNegImp p = let hyp = insert (p ~> Bot) (singleton p) in do
         s1 <- ax (p ~> Bot) hyp
         s2 <- ax p hyp
         s3 <- impE s1 s2
         impI (p ~> Bot) Bot s3

-- |- ((((p -> q) -> p) -> p) -> q) -> q (Int)
wkPeirce :: Formula -> Formula -> Maybe Sequent
wkPeirce p q = undefined

--------------------------------------------------------------------------
        --Classical Theorems
--------------------------------------------------------------------------

-- ~(p /\ q) |- ~p \/ ~q (Cl)
deMorgAnd :: Formula -> Formula -> Maybe Sequent
deMorgAnd p q = undefined

-- ~p \/ ~q |- ~(p /\ q) (Cl)
deMorgAnd' :: Formula -> Formula -> Maybe Sequent
deMorgAnd' p q = undefined

-- ~p \/ q |- p -> q (Cl)
orImp :: Formula -> Formula -> Maybe Sequent
orImp p q = undefined

-- |- p \/ ~p (Cl)
lem :: Formula -> Maybe Sequent
lem p = undefined

-- |- (((p -> q) -> p) -> p) -> q (Cl)
peirceL :: Formula -> Formula -> Maybe Sequent
peirceL p q = undefined

---------------------------------------------------------------------------
        --Tests
---------------------------------------------------------------------------

{--
testInt :: Test
testInt = "Intuitionistic Theorems" ~:
        TestList [ppt (andFlip (Var 'a') (Var 'b')) ~?= "a . b |- b . a",
                  ppt (orFlip (Var 'a') (Var 'b')) ~?= "a + b |- b + a",
                  ppt (distr1 (Var 'a') (Var 'b') (Var 'c'))
                        ~?= "a . (b + c) |- a . b + a . c"]
           where ppt = render . pp


instance PP Formula where
 pp Bot         = text "_|_"
 pp (Var c)     = char c
 pp (And f1 f2) = pp f1 <+> text "." <+> maybeParens (opCheck1 f2) (pp f2)
                      where  opCheck1 (Or _ _)  = True
                             opCheck1 (Imp _ _) = True
                             opCheck1 _         = False
 pp (Or f1 f2)  = pp f1 <+> text "+" <+> maybeParens (opCheck2 f2) (pp f2)
                      where  opCheck2 (Imp _ _) = True
                             opCheck2 _         = False
 pp (Imp f1 f2) = maybeParens (not(isAtomic f1)) (pp f1) <+> text "~>" <+> pp f2

instance PP (Maybe Sequent) where
  pp (Just seq) =
            hsep (map pp (toList (ctxt seq))) <+> text "|-" <+> pp (thes seq)
  pp Nothing    = text "No derivation"
--}

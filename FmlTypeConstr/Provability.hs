{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE GADTs         #-}
{-# LANGUAGE TypeOperators #-}

module FmlTypeConstr.Provability where

import             FmlTypeConstr.Basic

data Provable b a where
   Proof :: (HList b -> a) -> Provable b (Formula a)

----------------------------------------------------------------------
         --Intuitionistic Theorems using proof-terms
----------------------------------------------------------------------

-- p /\ ~p |- q
notTandFP :: Provable '[p :/\: (p :~>: Bot)]
                       (Formula q)
notTandFP = Proof $ \(HCons (AndT p (ImpT f)) HNil) -> abort (f p)

-- p /\ q |- q /\ p
andFlipP :: Provable '[p :/\: q]
                      (Formula (q :/\: p))
andFlipP = Proof $ \(HCons (AndT p1 p2) HNil) -> AndT p2 p1

-- p, q instantiated at specific formulas
andFlipPEx :: Provable '[TNat Z :/\: TNat (S Z)]
                        (Formula (TNat (S Z) :/\: TNat Z))
andFlipPEx = andFlipP

-- p \/ q |- q \/ p
orFlipP :: Provable '[p :\/: q]
                     (Formula (q :\/: p))
orFlipP = Proof $ \x -> case x of
                          (HCons (OrT1 p1) HNil) -> OrT2 p1
                          (HCons (OrT2 p2) HNil) -> OrT1 p2

-- p /\ (q \/ r) |- (p /\ q) \/ (p /\ r)
distr1P :: Provable '[p :/\: (q :\/: r)]
                    (Formula ((p :/\: q) :\/: (p :/\: r)))
distr1P = Proof $ \(HCons (AndT p qOrr) HNil) ->
                     case qOrr of
                      OrT1 q -> OrT1 (AndT p q)
                      OrT2 r -> OrT2 (AndT p r)

-- (p /\ q) \/ (p /\ r) |- p /\ (q \/ r)
distr1'P :: Provable '[(p :/\: q) :\/: (p :/\: r)]
                      (Formula (p :/\: (q :\/: r)))
distr1'P = Proof $ \(HCons x HNil) -> case x of
                          OrT1 (AndT p q) -> AndT p (OrT1 q)
                          OrT2 (AndT p r) -> AndT p (OrT2 r)

-- p \/ (q /\ r) |- (p \/ q) /\ (p \/ r)
distr2P :: Provable '[p :\/: (q :/\: r)]
                    (Formula ((p :\/: q) :/\: (p :\/: r)))
distr2P = Proof $ \(HCons x HNil) -> case x of
                         OrT1 p          -> AndT (OrT1 p) (OrT1 p)
                         OrT2 (AndT q r) -> AndT (OrT2 q) (OrT2 r)

-- (p \/ q) /\ (p \/ r) |- p \/ (q /\ r)
distr2'P :: Provable '[(p :\/: q) :/\: (p :\/: r)]
                      (Formula (p :\/: (q :/\: r)))
distr2'P = Proof $ \(HCons (AndT pq pr) HNil) -> case (pq, pr) of
                      (OrT1 p, _)      -> OrT1 p
                      (_, OrT1 p)      -> OrT1 p
                      (OrT2 q, OrT2 r) -> OrT2 (AndT q r)

-- p -> (q -> r), p -> q |- p -> r
impTransP :: Provable '[p :~>: q :~>: r,p :~>: q]
                       (Formula (p :~>: r))
impTransP = Proof $ \(HCons (ImpT f) (HCons (ImpT g) HNil)) ->
                         ImpT $ \p -> case f p of
                                   ImpT fp -> fp (g p)

-- p |- ~~p
doubNegImpP :: Provable '[p] (Formula ((p :~>: Bot) :~>: Bot))
doubNegImpP = Proof $ \(HCons p HNil) -> ImpT (\(ImpT f) -> f p)

-- ~(p \/ q) |- ~p /\ ~q
deMorIntP :: Provable '[(p :\/: q) :~>: Bot]
                       (Formula ((p :~>: Bot) :/\: (q :~>: Bot)))
deMorIntP = Proof $ \(HCons (ImpT f) HNil) ->
                      AndT (ImpT (\p -> f (OrT1 p)))
                           (ImpT (\q -> f (OrT2 q)))

-- ~p /\ ~q |- ~(p \/ q)
deMorInt'P :: Provable '[(p :~>: Bot) :/\: (q :~>: Bot)]
                        (Formula ((p :\/: q) :~>: Bot))
deMorInt'P = Proof $ \(HCons (AndT (ImpT f) (ImpT g)) HNil) ->
                      ImpT $ \x -> case x of
                                     OrT1 p -> f p
                                     OrT2 q -> g q

-- ~p \/ ~q |- ~(p /\ q)
deMor2'P :: Provable '[(p :~>: Bot) :\/: (q :~>: Bot)]
                     (Formula ((p :/\: q) :~>: Bot))
deMor2'P = Proof $ \(HCons x HNil) ->
                      case x of
                        OrT1 (ImpT f) -> ImpT (\(AndT p _) -> f p)
                        OrT2 (ImpT g) -> ImpT (\(AndT _ q) -> g q)

-- ~p \/ q |- p -> q 
orImpP :: Provable '[(p :~>: Bot) :\/: q]
                    (Formula (p :~>: q))
orImpP = Proof $ \(HCons x HNil) -> case x of
                                      OrT1 (ImpT f) -> ImpT (\p -> abort (f p))
                                      OrT2 q        -> ImpT (\_ -> q)

-- |- ((((p -> q) -> p) -> p) -> q) -> q
wkPeirceP :: Provable '[]
                     (Formula (((((p :~>: q) :~>: p) :~>: p) :~>: q) :~>: q))
wkPeirceP = Proof $ \HNil -> ImpT
                    (\(ImpT f) -> f (ImpT
                       (\(ImpT g) -> g (ImpT
                          (\p -> f (ImpT (\_ -> p)))))))

-----------------------------------------------------------------------

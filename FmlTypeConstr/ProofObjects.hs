{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE GADTs         #-}
{-# LANGUAGE PolyKinds     #-}
{-# LANGUAGE TypeOperators #-}

module FmlTypeConstr.ProofObjects where

import           FmlTypeConstr.Basic

---------------------------------------------------------------------
        --Intuitionistic Natural Deduction with Proof-terms
---------------------------------------------------------------------

data ProofObj where
     T     :: ProofObj
     Vbl   :: Nat -> ProofObj
     Pair  :: ProofObj -> ProofObj -> ProofObj
     Proj1 :: ProofObj -> ProofObj
     Proj2 :: ProofObj -> ProofObj
     Inj1  :: ProofObj -> ProofObj
     Inj2  :: ProofObj -> ProofObj
     Case  :: ProofObj -> ProofObj -> ProofObj -> ProofObj
                                   -> ProofObj -> ProofObj
     Lam   :: ProofObj -> ProofObj -> ProofObj
     App   :: ProofObj -> ProofObj -> ProofObj
     Abort :: ProofObj -> ProofObj

data ProofProp a = IsProof ProofObj a

data DerivesP ctx p a where

  TrP    :: -------------------------------------
            DerivesP ctx T (Formula Top)

  IdP    :: ----------------------------------------------
            DerivesP (IsProof x a : ctx) x (Formula a)

  WkP    :: DerivesP ctx p (Formula a) ->
            ---------------------------------------------
            DerivesP (IsProof x qc : ctx) p (Formula a)

  CnP    :: DerivesP (IsProof x qb : IsProof x qb : ctx) p (Formula a) ->
            --------------------------------------------------------------
            DerivesP (IsProof x qb : ctx) p (Formula a)

  ExP    :: DerivesP ctx1 T (Formula Top) ->
            DerivesP ctx2 T (Formula Top) ->
            DerivesP '[IsProof x1 qb1] T (Formula Top) ->
            DerivesP '[IsProof x2 qb2] T (Formula Top) ->
            DerivesP (ctx1 ++ (IsProof x1 qb1 : IsProof x2 qb2 : ctx2))
                                                      p (Formula a) ->
            --------------------------------------------------------------
            DerivesP (ctx1 ++ (IsProof x2 qb2 : IsProof x1 qb1 : ctx2))
                                                      p (Formula a)

  AndIP  :: DerivesP ctx p1 (Formula a1) ->
            DerivesP ctx p2 (Formula a2) ->
            -------------------------------------------------
            DerivesP ctx (Pair p1 p2) (Formula (a1 :/\: a2))

  AndE1P :: DerivesP ctx p (Formula (a1 :/\: a2)) ->
            -----------------------------------------
            DerivesP ctx (Proj1 p) (Formula a1)

  AndE2P :: DerivesP ctx p (Formula (a1 :/\: a2)) ->
            -----------------------------------------
            DerivesP ctx (Proj2 p) (Formula a2)

  OrI1P  :: DerivesP ctx p (Formula a1) ->
            --------------------------------------------
            DerivesP ctx (Inj1 p) (Formula (a1 :\/: a2))

  OrI2P  :: DerivesP ctx p (Formula a2) ->
            --------------------------------------------
            DerivesP ctx (Inj2 p) (Formula (a1 :\/: a2))

  OrEP   :: DerivesP (IsProof x1 a1 : ctx) q1 (Formula a) ->
            DerivesP (IsProof x2 a2 : ctx) q2 (Formula a) ->
            DerivesP ctx p (Formula (a1 :\/: a2)) ->
            ----------------------------------------------------------
            DerivesP ctx (Case p x1 q1 x2 q2) (Formula a)

  ImpIP  :: DerivesP (IsProof p a : ctx) q (Formula b) ->
            ----------------------------------------------------------
            DerivesP ctx (Lam p q) (Formula (a :~>: b))

  ImpEP  :: DerivesP ctx p (Formula (a :~>: b)) ->
            DerivesP ctx q (Formula a) ->
            --------------------------------------
            DerivesP ctx (App p q) (Formula b)

  BotEP  :: DerivesP ctx p (Formula Bot) ->
            --------------------------------------
            DerivesP ctx (Abort p) (Formula a)

---------------------------------------------------------------------
        --Proving theorems with Proof-Objects
---------------------------------------------------------------------

-- |- T : Top
empDerTrP :: DerivesP '[] T (Formula Top)
empDerTrP = TrP

-- (x1 : p), (x2 : q), (x3 : r), (x4 : s), ... |- x : r <=>
-- (x2 : q), (x1 : p), (x3 : r), (x4 : s), ... |- x : r
flipCtxP :: DerivesP  (IsProof x1 p : IsProof x2 q : ctx) x (Formula r) ->
            DerivesP  (IsProof x2 q : IsProof x1 p : ctx) x (Formula r)
flipCtxP t = ExP empDerTrP TrP TrP TrP t

-- x : p |- x : p
pImppP :: DerivesP '[IsProof x p] x (Formula p)
pImppP = IdP

-- x : p /\ ~p |- abort((snd x) . (fst x)) : q
notTandFPP :: DerivesP '[IsProof x (p :/\: (p :~>: Bot))]
                      (Abort (App (Proj2 x) (Proj1 x)))
                      (Formula q)
notTandFPP = BotEP (ImpEP (AndE2P IdP) (AndE1P IdP))

-- x : p /\ (q \/ r) |- case (snd x)
--                         { x1 -> i1 (fst x, x1) |
--                           x2 -> i2 (fst x, x2) } : (p /\ q) \/ (p /\ r)
distr1PP :: DerivesP '[IsProof x (p :/\: (q :\/: r))]
                      (Case (Proj2 x)
                         x1 (Inj1 (Pair (Proj1 x) x1))
                         x2 (Inj2 (Pair (Proj1 x) x2)))
                      (Formula ((p :/\: q) :\/: (p :/\: r)))
distr1PP = OrEP (OrI1P (AndIP (AndE1P a) IdP))
                (OrI2P (AndIP (AndE1P a) IdP))
                (AndE2P IdP)
     where a = flipCtxP IdP

-- x : (p \/ q) /\ (p \/ r) |- case (snd x)
--                              {x1 -> i1 x1
--                               x2 -> case (fst x)
--                                      {x1' -> i1 x1'
--                                       x2' -> i2 (x2', x2)} } : p \/ (q /\ r)
distr2'PP :: DerivesP '[IsProof x ((p :\/: q) :/\: (p :\/: r))]
                       (Case (Proj2 x)
                            x1 (Inj1 x1)
                            x2 (Case (Proj1 x)
                                  x1' (Inj1 x1')
                                  x2' (Inj2 (Pair x2' x2))))
                      (Formula (p :\/: (q :/\: r)))
distr2'PP = OrEP (OrI1P IdP)
               (OrEP (OrI1P IdP) (OrI2P (AndIP IdP (flipCtxP IdP)))
                                             (flipCtxP (AndE1P IdP)))
               (AndE2P IdP)

-- x : ~(p \/ q) |- (\y0. x (i1 y0), \z0. x (i2 z0)) : ~p /\ ~q
deMorIntPP :: DerivesP '[IsProof x ((p :\/: q) :~>: Bot)]
                        (Pair (Lam y0 (App x (Inj1 y0)))
                              (Lam z0 (App x (Inj2 z0))))
                       (Formula ((p :~>: Bot) :/\: (q :~>: Bot)))
deMorIntPP = AndIP (ImpIP (ImpEP (flipCtxP IdP) (OrI1P IdP)))
                   (ImpIP (ImpEP (flipCtxP IdP) (OrI2P IdP)))

-- |- (\y0. y0 (\y1. y1 (\y2. y0 (\y3. y2)))) :
--                           ((((p -> q) -> p) -> p) -> q) -> q
wkPeircePP :: DerivesP '[]
              (Lam y0 (App y0 (Lam y1 (App y1 (Lam y2 (App y0 (Lam y3 y2)))))))
              (Formula (((((p :~>: q) :~>: p) :~>: p) :~>: q) :~>: q))
wkPeircePP = ImpIP (ImpEP IdP
                   (ImpIP (ImpEP IdP
                            (ImpIP (ImpEP (ExP a0 TrP TrP TrP (flipCtxP IdP))
                                   (ImpIP (flipCtxP IdP)))))))
           where a0 :: DerivesP '[IsProof x p] T (Formula Top)
                 a0 = TrP

---------------------------------------------------------------------------

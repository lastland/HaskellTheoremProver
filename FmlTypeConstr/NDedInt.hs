{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE GADTs         #-}
{-# LANGUAGE PolyKinds     #-}
{-# LANGUAGE TypeOperators #-}

module FmlTypeConstr.NDedInt where

import           FmlTypeConstr.Basic

------------------------------------------------------------
        --Intuitionistic Natural Deduction Rules
------------------------------------------------------------


data DerivesI (ctx :: [*]) a where

  Tr    :: -------------------------------------
           DerivesI ctx (Formula Top)

  Id    :: --------------------------------------
           DerivesI (Formula a : ctx) (Formula a)

  Wk    :: DerivesI ctx (Formula a) ->
           --------------------------------------
           DerivesI (Formula c : ctx) (Formula a)

  Cn    :: DerivesI (b : b : ctx) (Formula a) ->
           --------------------------------------
           DerivesI (b : ctx) (Formula a)

  Ex    :: DerivesI ctx1 (Formula Top) ->
           DerivesI ctx2 (Formula Top) ->
           DerivesI '[b1] (Formula Top) ->
           DerivesI '[b2] (Formula Top) ->
           DerivesI (ctx1 ++ (b1 : b2 : ctx2)) (Formula a) ->
           ---------------------------------------------------
           DerivesI (ctx1 ++ (b2 : b1 : ctx2)) (Formula a)

  AndI  :: DerivesI ctx (Formula a1) ->
           DerivesI ctx (Formula a2) ->
           ------------------------------------
           DerivesI ctx (Formula (a1 :/\: a2))

  AndE1 :: DerivesI ctx (Formula (a1 :/\: a2)) ->
           ---------------------------------------
           DerivesI ctx (Formula a1)

  AndE2 :: DerivesI ctx (Formula (a1 :/\: a2)) ->
           ---------------------------------------
           DerivesI ctx (Formula a2)

  OrI1  :: DerivesI ctx (Formula a1) ->
           -------------------------------------
           DerivesI ctx (Formula (a1 :\/: a2))

  OrI2  :: DerivesI ctx (Formula a2) ->
           --------------------------------------
           DerivesI ctx (Formula (a1 :\/: a2))

  OrE   :: DerivesI (Formula a1 : ctx) (Formula a) ->
           DerivesI (Formula a2 : ctx) (Formula a) ->
           DerivesI ctx (Formula (a1 :\/: a2)) ->
           -------------------------------------------
           DerivesI ctx (Formula a)

  ImpI  :: DerivesI (Formula a : ctx) (Formula b) ->
           -------------------------------------------
           DerivesI ctx (Formula (a :~>: b))

  ImpE  :: DerivesI ctx (Formula (a :~>: b)) ->
           DerivesI ctx (Formula a) ->
           --------------------------------------
           DerivesI ctx (Formula b)

  BotE  :: DerivesI ctx (Formula Bot) ->
           --------------------------------------
           DerivesI ctx (Formula a)

----------------------------------------------------------------
        -- Intuitionistic Theorems
----------------------------------------------------------------

-- |- T
empDerTr :: DerivesI '[] (Formula Top)
empDerTr = Tr

-- p, q, r, s, ... |- r <=> q, p, r, s, ... |- r
flipCtx :: DerivesI  (Formula p : Formula q : ctx) (Formula r) ->
           DerivesI  (Formula q : Formula p : ctx) (Formula r)
flipCtx t = Ex empDerTr Tr Tr Tr t

-- p |- p
pImpp :: DerivesI '[Formula p] (Formula p)
pImpp = Id

-- p /\ ~p |- q
notTandFA :: DerivesI '[Formula (p :/\: (p :~>: Bot))]
                      (Formula q)
notTandFA = BotE (ImpE (AndE2 Id) (AndE1 Id))

-- p /\ q |- q /\ p (Proposition level)
andFlipA :: DerivesI '[Formula (p :/\: q)]
                     (Formula (q :/\: p))
andFlipA = AndI (AndE2 Id) (AndE1 Id)

-- p, q instantiated at specific formulas
andFlipAEx :: DerivesI '[Formula (TNat Z :/\: TNat (S Z))]
                       (Formula (TNat (S Z) :/\: TNat Z))
andFlipAEx = andFlipA


-- p \/ q |- q \/ p (Proposition level)
orFlipA :: DerivesI '[Formula (p :\/: q)]
                    (Formula (q :\/: p))
orFlipA = OrE (OrI2 Id) (OrI1 Id) Id


-- p /\ (q \/ r) |- (p /\ q) \/ (p /\ r) (Proposition level)
distr1A :: DerivesI '[Formula (p :/\: (q :\/: r))]
                    (Formula ((p :/\: q) :\/: (p :/\: r)))
distr1A = OrE (OrI1 (AndI (AndE1 a) Id))
              (OrI2 (AndI (AndE1 a) Id))
              (AndE2 Id)
     where a = flipCtx Id


-- (p /\ q) \/ (p /\ r) |- p /\ (q \/ r) (Proposition level)
distr1'A :: DerivesI '[Formula ((p :/\: q) :\/: (p :/\: r))]
                      (Formula (p :/\: (q :\/: r)))
distr1'A = OrE (AndI (AndE1 Id) (OrI1 (AndE2 Id)))
               (AndI (AndE1 Id) (OrI2 (AndE2 Id)))
               Id


-- p \/ (q /\ r) |- (p \/ q) /\ (p \/ r) (Proposition level)
distr2A :: DerivesI '[Formula (p :\/: (q :/\: r))]
                    (Formula ((p :\/: q) :/\: (p :\/: r)))
distr2A = AndI (OrE (OrI1 Id) (OrI2 (AndE1 Id)) Id)
               (OrE (OrI1 Id) (OrI2 (AndE2 Id)) Id)


-- (p \/ q) /\ (p \/ r) |- p \/ (q /\ r) (Proposition level)
distr2'A :: DerivesI '[Formula ((p :\/: q) :/\: (p :\/: r))]
                      (Formula (p :\/: (q :/\: r)))
distr2'A = OrE (OrI1 Id)
               (OrE (OrI1 Id) (OrI2 (AndI Id (flipCtx Id)))
                                             (flipCtx (AndE1 Id)))
               (AndE2 Id)


-- p -> (q -> r), p -> q |- p -> r (Proposition level)
impTransA :: DerivesI '[Formula (p :~>: q :~>: r),Formula (p :~>: q)]
                      (Formula (p :~>: r))
impTransA = ImpI (ImpE (ImpE (flipCtx Id) Id)
                      (ImpE (Ex a1 Tr Tr Tr (flipCtx Id)) Id))
           where a1 :: DerivesI '[Formula p] (Formula Top)
                 a1 = Tr


-- p |- ~~p (Proposition level)
doubNegImpA :: DerivesI '[Formula p]
                         (Formula ((p :~>: Bot) :~>: Bot))
doubNegImpA = ImpI (ImpE Id (flipCtx Id))


-- ~(p \/ q) |- ~p /\ ~q (Proposition level)
deMorIntA :: DerivesI '[Formula ((p :\/: q) :~>: Bot)]
                       (Formula ((p :~>: Bot) :/\: (q :~>: Bot)))
deMorIntA = AndI (ImpI (ImpE (flipCtx Id) (OrI1 Id)))
                 (ImpI (ImpE (flipCtx Id) (OrI2 Id)))


-- ~p /\ ~q |- ~(p \/ q) (Proposition level)
deMorInt'A :: DerivesI '[Formula ((p :~>: Bot) :/\: (q :~>: Bot))]
                        (Formula ((p :\/: q) :~>: Bot))
deMorInt'A = ImpI (flipCtx (OrE (ImpE (flipCtx (AndE1 Id)) Id)
                                (ImpE (flipCtx (AndE2 Id)) Id)
                                (flipCtx Id)))


-- ~p \/ ~q |- ~(p /\ q) (Proposition level)
deMor2'A :: DerivesI '[Formula ((p :~>: Bot) :\/: (q :~>: Bot))]
                     (Formula ((p :/\: q) :~>: Bot))
deMor2'A = ImpI (OrE (ImpE Id (flipCtx (AndE1 Id)))
                      (ImpE Id (flipCtx (AndE2 Id)))
                      (flipCtx Id))


-- ~p \/ q |- p -> q (Proposition level)
orImpA :: DerivesI '[Formula ((p :~>: Bot) :\/: q)]
                    (Formula (p :~>: q))
orImpA = ImpI (flipCtx (OrE
                   (BotE (ImpE Id (Ex a1 Tr Tr Tr (flipCtx Id)))) Id Id))
         where
                a1 :: DerivesI '[Formula (p :~>: Bot)] (Formula Top)
                a1 = Tr


-- |- ((((p -> q) -> p) -> p) -> q) -> q (Proposition level)
wkPeirceA :: DerivesI '[]
                     (Formula (((((p :~>: q) :~>: p) :~>: p) :~>: q) :~>: q))
wkPeirceA = ImpI (ImpE Id
                   (ImpI (ImpE Id
                            (ImpI (ImpE (Ex a0 Tr Tr Tr (flipCtx Id))
                                  (ImpI (flipCtx Id)))))))
           where a0 :: DerivesI '[Formula p] (Formula Top)
                 a0 = Tr

---------------------------------------------------------------------------

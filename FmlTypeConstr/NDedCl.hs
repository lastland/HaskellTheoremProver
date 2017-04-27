{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE GADTs         #-}
{-# LANGUAGE PolyKinds     #-}
{-# LANGUAGE TypeOperators #-}

module FmlTypeConstr.NDedCl where

import           FmlTypeConstr.Basic
import           FmlTypeConstr.NDedInt

-----------------------------------------------------------
        --Classical Natural Deduction Rules
-----------------------------------------------------------

data DerivesC (ctx :: [*]) a where

  TrC    ::  -------------------------------------
             DerivesC ctx (Formula Top)

  IdC    ::  --------------------------------------
             DerivesC (Formula a : ctx) (Formula a)

  WkC    ::  DerivesC ctx (Formula a) ->
             --------------------------------------
             DerivesC (Formula c : ctx) (Formula a)

  CnC    ::  DerivesC (b : b : ctx) (Formula a) ->
             --------------------------------------
             DerivesC (b : ctx) (Formula a)

  ExC    ::  DerivesC ctx1 (Formula Top) ->
             DerivesC ctx2 (Formula Top) ->
             DerivesC '[b1] (Formula Top) ->
             DerivesC '[b2] (Formula Top) ->
             DerivesC (ctx1 ++ (b1 : b2 : ctx2)) (Formula a) ->
             ---------------------------------------------------
             DerivesC (ctx1 ++ (b2 : b1 : ctx2)) (Formula a)

  AndIC  ::  DerivesC ctx (Formula a1) ->
             DerivesC ctx (Formula a2) ->
             ------------------------------------
             DerivesC ctx (Formula (a1 :/\: a2))

  AndE1C ::  DerivesC ctx (Formula (a1 :/\: a2)) ->
             ---------------------------------------
             DerivesC ctx (Formula a1)

  AndE2C ::  DerivesC ctx (Formula (a1 :/\: a2)) ->
             ---------------------------------------
             DerivesC ctx (Formula a2)

  OrI1C  ::  DerivesC ctx (Formula a1) ->
             -------------------------------------
             DerivesC ctx (Formula (a1 :\/: a2))

  OrI2C  ::  DerivesC ctx (Formula a2) ->
             --------------------------------------
             DerivesC ctx (Formula (a1 :\/: a2))

  OrEC   ::  DerivesC (Formula a1 : ctx) (Formula a) ->
             DerivesC (Formula a2 : ctx) (Formula a) ->
             DerivesC ctx (Formula (a1 :\/: a2)) ->
             -------------------------------------------
             DerivesC ctx (Formula a)

  ImpIC  ::  DerivesC (Formula a : ctx) (Formula b) ->
             -------------------------------------------
             DerivesC ctx (Formula (a :~>: b))

  ImpEC  ::  DerivesC ctx (Formula (a :~>: b)) ->
             DerivesC ctx (Formula a) ->
             --------------------------------------
             DerivesC ctx (Formula b)

  Dne    ::  DerivesC ctx (Formula ((a :~>: Bot) :~>: Bot)) ->
             --------------------------------------------------
             DerivesC ctx (Formula a)


----------------------------------------------------------------
        -- Classical Theorems
----------------------------------------------------------------

-- Intuitionistic formulas are classically true
int2C :: DerivesI ctx (Formula a) -> DerivesC ctx (Formula a)
int2C Tr                        = TrC
int2C Id                        = IdC
int2C (Wk s)                    = WkC (int2C s)
int2C (Cn s)                    = CnC (int2C s)
int2C (Ex s1 s2 s3 s4 s5)       = ExC (int2C s1) (int2C s2) (int2C s3)
                                                 (int2C s4) (int2C s5)
int2C (AndI s1 s2)              = AndIC (int2C s1) (int2C s2)
int2C (AndE1 s)                 = AndE1C (int2C s)
int2C (AndE2 s)                 = AndE2C (int2C s)
int2C (OrI1 s)                  = OrI1C (int2C s)
int2C (OrI2 s)                  = OrI2C (int2C s)
int2C (OrE s1 s2 s3)            = OrEC (int2C s1) (int2C s2) (int2C s3)
int2C (ImpI s)                  = ImpIC (int2C s)
int2C (ImpE s1 s2)              = ImpEC (int2C s1) (int2C s2)
int2C (BotE s)                  = Dne (ImpIC (WkC (int2C s)))

-- |- T
empDerTrC :: DerivesC '[] (Formula Top)
empDerTrC = TrC

-- p, q, r, s, ... |- r <=> q, p, r, s, ... |- r
flipCtxC :: DerivesC  (Formula p : Formula q : ctx) (Formula r) ->
            DerivesC  (Formula q : Formula p : ctx) (Formula r)
flipCtxC t = ExC empDerTrC TrC TrC TrC t

-- |- p \/ ~p
lem :: DerivesC '[]
                 (Formula (p :\/: (p :~>: Bot)))
lem = Dne (ImpIC (ImpEC (AndE1C dm) (Dne (AndE2C dm))))
       where dm = int2C deMorIntA

-- |- ((p -> q) -> p) -> p
peirceL :: DerivesC '[]
                     (Formula (((p :~>: q) :~>: p) :~>: p))
peirceL = ImpIC $ OrEC IdC
               (ImpEC (flipCtxC IdC)
                      (int2C (ImpI (BotE (ImpE (flipCtx Id) Id)))))
               (WkC lem)

-- p -> q |- ~p \/ q
impOr :: DerivesC '[Formula (p :~>: q)]
                   (Formula ((p :~>: Bot) :\/: q))
impOr = OrEC (OrI2C (ImpEC (flipCtxC IdC) IdC))
             (OrI1C IdC) (WkC lem)

-- ~(p /\ q) |- ~p \/ ~q
deMorC :: DerivesC '[Formula ((p :/\: q) :~>: Bot)]
                   (Formula ((p :~>: Bot) :\/: (q :~>: Bot)))
deMorC = OrEC (OrI2C (ImpIC (ImpEC (ExC a0 TrC TrC TrC (flipCtxC IdC))
                                     (AndIC (flipCtxC IdC) IdC))))
               (OrI1C IdC) (WkC lem)
          where a0 :: DerivesC '[Formula q] (Formula Top)
                a0 = TrC

--------------------------------------------------------------------------


{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}

module GStyleInt where

import Basic

-----------------------------------------------------------------------
          --Gentzen style cut-free sequent calculus (intuitionistic)
-----------------------------------------------------------------------

data DerivesGI (ctx :: [*]) a where

  TrGI  :: -------------------------------------
           DerivesGI ctx (Formula Top)

  BotGI :: -----------------------------------------
           DerivesGI (Formula Bot : ctx) (Formula a)
  
  IdGI  :: --------------------------------------
           DerivesGI (Formula a : ctx) (Formula a)
  
  WkL   :: DerivesGI ctx (Formula a) ->
           --------------------------------------
           DerivesGI (Formula c : ctx) (Formula a)

  CnL   :: DerivesGI (b : b : ctx) (Formula a) ->
           ---------------------------------------
           DerivesGI (b : ctx) (Formula a)
        
  ExL   :: DerivesGI ctx1 (Formula Top) ->
           DerivesGI ctx2 (Formula Top) ->
           DerivesGI '[b1] (Formula Top) ->
           DerivesGI '[b2] (Formula Top) ->
           DerivesGI (ctx1 ++ (b1 : b2 : ctx2)) (Formula a) ->
           ----------------------------------------------------
           DerivesGI (ctx1 ++ (b2 : b1 : ctx2)) (Formula a)
        
  AndR  :: DerivesGI ctx (Formula a1) ->
           DerivesGI ctx (Formula a2) ->
           ------------------------------------
           DerivesGI ctx (Formula (a1 :/\: a2))
          
  AndL1 :: DerivesGI (Formula a1 : ctx) (Formula a) ->
           -------------------------------------------------
           DerivesGI (Formula (a1 :/\: a2) : ctx) (Formula a)
  
  AndL2 :: DerivesGI (Formula a2 : ctx) (Formula a) ->
           -------------------------------------------------
           DerivesGI (Formula (a1 :/\: a2) : ctx) (Formula a)
  
  OrR1  :: DerivesGI ctx (Formula a1) ->
           -------------------------------------
           DerivesGI ctx (Formula (a1 :\/: a2))
  
  OrR2  :: DerivesGI ctx (Formula a2) ->
           --------------------------------------
           DerivesGI ctx (Formula (a1 :\/: a2))
  
  OrL   :: DerivesGI (Formula a1 : ctx) (Formula a) ->
           DerivesGI (Formula a2 : ctx) (Formula a) ->
           ---------------------------------------------------
           DerivesGI (Formula (a1 :\/: a2) : ctx) (Formula a)
           
  ImpR  :: DerivesGI (Formula a : ctx) (Formula b) ->
           -------------------------------------------
           DerivesGI ctx (Formula (a :~>: b))
           
  ImpL  :: DerivesGI ctx (Formula a) ->
           DerivesGI (Formula b : ctx) (Formula c) ->
           ------------------------------------------------
           DerivesGI (Formula (a :~>: b) : ctx) (Formula c)


-----------------------------------------------------------------
           --Some Intuitionistic Theorems (Gentzen style proof)
-----------------------------------------------------------------

-- |- T    
empDerTrG :: DerivesGI '[] (Formula Top)
empDerTrG = TrGI

-- p, q, r, s, ... |- r <=> q, p, r, s, ... |- r
flipCtxG :: DerivesGI  (Formula p : Formula q : ctx) (Formula r) ->
            DerivesGI  (Formula q : Formula p : ctx) (Formula r)
flipCtxG t = ExL empDerTrG TrGI TrGI TrGI t


-- p /\ (q \/ r) |- (p /\ q) \/ (p /\ r) 
distr1G :: DerivesGI '[Formula (p :/\: (q :\/: r))]
                    (Formula ((p :/\: q) :\/: (p :/\: r)))
distr1G = CnL (AndL1 (flipCtxG (AndL2 (OrL (OrR1 (AndR (flipCtxG IdGI) IdGI))
                                       (OrR2 (AndR (flipCtxG IdGI) IdGI))))))

-- (p /\ q) \/ (p /\ r) |- p /\ (q \/ r) 
distr1'G :: DerivesGI '[Formula ((p :/\: q) :\/: (p :/\: r))]
                      (Formula (p :/\: (q :\/: r)))
distr1'G = OrL (AndR (AndL1 IdGI) (AndL2 (OrR1 IdGI)))
               (AndR (AndL1 IdGI) (AndL2 (OrR2 IdGI)))

-- ~(p \/ q) |- ~p /\ ~q 
deMorIntG :: DerivesGI '[Formula ((p :\/: q) :~>: Bot)]
                       (Formula ((p :~>: Bot) :/\: (q :~>: Bot)))
deMorIntG = AndR (ImpR (flipCtxG (ImpL (OrR1 IdGI) IdGI)))
                 (ImpR (flipCtxG (ImpL (OrR2 IdGI) IdGI)))

-- ~p \/ q |- p -> q 
orImpG :: DerivesGI '[Formula ((p :~>: Bot) :\/: q)]
                    (Formula (p :~>: q))
orImpG = OrL (ImpR (flipCtxG (ImpL IdGI BotGI))) (ImpR (flipCtxG IdGI))
          
-- |- ((((p -> q) -> p) -> p) -> q) -> q
wkPeirceG :: DerivesGI '[]
                     (Formula (((((p :~>: q) :~>: p) :~>: p) :~>: q) :~>: q))
wkPeirceG = ImpR (CnL (ImpL (ImpR (CnL (ImpL (ImpR
                 (ExL a TrGI TrGI TrGI (flipCtxG
                 (ImpL (ImpR (flipCtxG IdGI)) IdGI)))) IdGI))) IdGI))
  where    a :: DerivesGI '[Formula p] (Formula Top)
           a = TrGI


--------------------------------------------------------------------------

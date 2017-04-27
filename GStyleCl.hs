
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}              
      
module GStyleCl where
                
import Basic
  
------------------------------------------------------------------
         --Gentzen style cut-free sequent calculus (Classical)
------------------------------------------------------------------

           
data DerivesGC (ctxl :: [*]) (ctxr :: [*])  where

  TrGC  :: -------------------------------------
           DerivesGC ctxl (Formula Top : ctxr)

  BotGC :: -------------------------------------
           DerivesGC (Formula Bot : ctxl) ctxr
  
  IdGC  :: -----------------------------------------------
           DerivesGC (Formula a : ctxl) (Formula a : ctxr)
  
  WkLC  :: DerivesGC ctxl ctxr ->
           -----------------------------------
           DerivesGC (Formula a : ctxl) ctxr

  WkRC  :: DerivesGC ctxl ctxr ->
           -----------------------------------
           DerivesGC ctxl (Formula a : ctxr)

  CnLC  :: DerivesGC (b : b : ctxl) ctxr ->
           ----------------------------------
           DerivesGC (b : ctxl) ctxr

  CnRC  :: DerivesGC ctxl (b : b : ctxr) ->
           ----------------------------------
           DerivesGC ctxl (b : ctxr)
        
  ExLC  :: DerivesGC ctx1 '[Formula Top] ->
           DerivesGC ctx2 '[Formula Top] ->
           DerivesGC '[b1] '[Formula Top] ->
           DerivesGC '[b2] '[Formula Top] ->
           DerivesGC (ctx1 ++ (b1 : b2 : ctx2)) ctxr ->
           -----------------------------------------------
           DerivesGC (ctx1 ++ (b2 : b1 : ctx2)) ctxr
           
  ExRC  :: DerivesGC '[Formula Bot] ctx1 ->
           DerivesGC '[Formula Bot] ctx2 ->
           DerivesGC '[Formula Bot] '[b1] ->
           DerivesGC '[Formula Bot] '[b2] ->
           DerivesGC ctxl (ctx1 ++ (b1 : b2 : ctx2)) ->
           ------------------------------------------------
           DerivesGC ctxl (ctx1 ++ (b2 : b1 : ctx2))
        
  AndRC :: DerivesGC ctxl (Formula a1 : ctxr) ->
           DerivesGC ctxl (Formula a2 : ctxr) ->
           --------------------------------------------
           DerivesGC ctxl (Formula (a1 :/\: a2) : ctxr)
          
  AndL1C :: DerivesGC (Formula a1 : ctxl) ctxr ->
            -----------------------------------------------
            DerivesGC (Formula (a1 :/\: a2) : ctxl) ctxr
  
  AndL2C :: DerivesGC (Formula a2 : ctxl) ctxr ->
            -----------------------------------------------
            DerivesGC (Formula (a1 :/\: a2) : ctxl) ctxr
  
  OrR1C :: DerivesGC ctxl (Formula a1 : ctxr) ->
           --------------------------------------------
           DerivesGC ctxl (Formula (a1 :\/: a2) : ctxr)
  
  OrR2C :: DerivesGC ctxl (Formula a2 : ctxr) ->
           --------------------------------------------
           DerivesGC ctxl (Formula (a1 :\/: a2) : ctxr)
  
  OrLC  :: DerivesGC (Formula a1 : ctxl) (Formula a : ctxr) ->
           DerivesGC (Formula a2 : ctxl) (Formula a : ctxr) ->
           ---------------------------------------------------
           DerivesGC (Formula (a1 :\/: a2) : ctxl) ctxr
           
  ImpRC :: DerivesGC (Formula a : ctxl) (Formula b : ctxr) ->
           ---------------------------------------------------
           DerivesGC ctxl (Formula (a :~>: b) : ctxr)
           
  ImpLC :: DerivesGC ctxl (Formula a : ctxr) ->
           DerivesGC (Formula b : ctxl) ctxr ->
           --------------------------------------------
           DerivesGC (Formula (a :~>: b) : ctxl) ctxr


----------------------------------------------------------------------
        --Some classical Theorems (Gentzen style proof)
----------------------------------------------------------------------

-- |- T, ctxr    
empDerTrGC :: DerivesGC '[] (Formula Top : ctxr)
empDerTrGC = TrGC

-- Bot, ctxl |- '[]
contrDerEmp :: DerivesGC (Formula Bot : ctxl) '[]
contrDerEmp = BotGC

-- p, q, ctxl |- ctxr <=> q, p, ctxl |- ctxr
flipCtxLC :: DerivesGC (Formula p : Formula q : ctxl) ctxr ->
             DerivesGC (Formula q : Formula p : ctxl) ctxr
flipCtxLC = ExLC empDerTrGC TrGC TrGC TrGC

-- ctxl |- r, s, ctxr <=> ctxl |- s, r, ctxr
flipCtxRC :: DerivesGC ctxl (Formula r : Formula s : ctxr) ->
             DerivesGC ctxl (Formula s : Formula r : ctxr)
flipCtxRC = ExRC contrDerEmp BotGC BotGC BotGC 

-- |- p \/ ~p (Gentzen Style)
lemG :: DerivesGC '[]
                 '[Formula (p :\/: (p :~>: Bot))]
lemG = CnRC (OrR1C (flipCtxRC (OrR2C (ImpRC (flipCtxRC IdGC)))))

-- |- ((p -> q) -> p) -> p (Gentzen Style)
peirceLG :: DerivesGC '[]
                     '[Formula (((p :~>: q) :~>: p) :~>: p)]
peirceLG = ImpRC (CnLC (ImpLC (ImpRC (flipCtxRC IdGC)) IdGC))
   
-- p -> q |- ~p \/ q (Gentzen Style)
impOrG :: DerivesGC '[Formula (p :~>: q)]
                    '[Formula ((p :~>: Bot) :\/: q)]
impOrG = CnLC (ImpLC (flipCtxRC (OrR1C (ImpRC (flipCtxRC IdGC)))) (OrR2C IdGC))

-- ~(p /\ q) |- ~p \/ ~q
deMorG :: DerivesGC '[Formula ((p :/\: q) :~>: Bot)]
                   '[Formula ((p :~>: Bot) :\/: (q :~>: Bot))]
deMorG = CnRC (OrR1C (ImpRC (flipCtxRC (flipCtxLC (OrR2C
         (ImpRC (flipCtxLC (ImpLC (AndRC (flipCtxLC IdGC) IdGC) BotGC))))))))

------------------------------------------------------------------------------


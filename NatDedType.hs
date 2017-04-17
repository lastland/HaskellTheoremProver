{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds, TypeOperators #-}

{-# OPTIONS -fwarn-incomplete-patterns #-}
    
module NatDedType where

import Text.PrettyPrint

data Bot 
data Top where
   One :: Top

data a :/\: b = AndT a b
data a :\/: b = OrT1 a | OrT2 b
data a :~>: b = ImpT (a -> b)

abort :: Bot -> a
abort x = case x of {}

data Nat = Z | S Nat

data SNat n where
   SZ :: SNat Z
   SS :: SNat n -> SNat (S n)

data HList :: [*] -> * where
  HNil  :: HList '[]
  HCons :: a -> HList t -> HList (a ': t)

type family (++) (f :: [*]) (g :: [*]) :: [*] where
       '[]      ++ l2  = l2
       (a : as) ++ l2  = a : (as ++ l2)


infixr 1 :~>:
infixr 2 :\/:
infixr 3 :/\:

data Formula (a :: *) where
     Contr :: Formula Bot
     Truth :: Formula Top
     Var   :: SNat n -> Formula (SNat n)
     And :: Formula a -> Formula b -> Formula (a :/\: b)
     Or  :: Formula a -> Formula b -> Formula (a :\/: b)
     Imp :: Formula a -> Formula b -> Formula (a :~>: b)

     
data Provable b a where
   Proof :: (HList b -> a) -> Provable b (Formula a)

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

-- p /\ ~p |- q (Proposition level)
notTandFA :: DerivesI '[Formula (p :/\: (p :~>: Bot))]
                      (Formula q)
notTandFA = BotE (ImpE (AndE2 Id) (AndE1 Id))

-- p /\ ~p |- q (Proof-term level)
notTandFP :: Provable '[p :/\: (p :~>: Bot)]
                       (Formula q)
notTandFP = Proof $ \(HCons (AndT p (ImpT f)) HNil) -> abort (f p)  

-- p /\ q |- q /\ p (Proposition level) 
andFlipA :: DerivesI '[Formula (p :/\: q)]
                     (Formula (q :/\: p))
andFlipA = AndI (AndE2 Id) (AndE1 Id)
         
-- p, q instantiated at specific formulas
andFlipAEx :: DerivesI '[Formula (SNat Z :/\: SNat (S Z))]
                       (Formula (SNat (S Z) :/\: SNat Z))
andFlipAEx = andFlipA

-- p /\ q |- q /\ p (Proof-term level)
andFlipP :: Provable '[p :/\: q]
                      (Formula (q :/\: p))
andFlipP = Proof $ \(HCons (AndT p1 p2) HNil) -> AndT p2 p1

-- p, q instantiated at specific formulas
andFlipPEx :: Provable '[SNat Z :/\: SNat (S Z)]
                        (Formula (SNat (S Z) :/\: SNat Z))
andFlipPEx = andFlipP

-- p \/ q |- q \/ p (Proposition level)
orFlipA :: DerivesI '[Formula (p :\/: q)]
                    (Formula (q :\/: p))
orFlipA = OrE (OrI2 Id) (OrI1 Id) Id

-- p \/ q |- q \/ p (Proof-term level)
orFlipP :: Provable '[p :\/: q]
                     (Formula (q :\/: p))
orFlipP = Proof $ \x -> case x of
                          (HCons (OrT1 p1) HNil) -> OrT2 p1
                          (HCons (OrT2 p2) HNil) -> OrT1 p2
        
-- p /\ (q \/ r) |- (p /\ q) \/ (p /\ r) (Proposition level)
distr1A :: DerivesI '[Formula (p :/\: (q :\/: r))]
                    (Formula ((p :/\: q) :\/: (p :/\: r)))
distr1A = OrE (OrI1 (AndI (AndE1 a1) Id))
              (OrI2 (AndI (AndE1 a2) Id))
              (AndE2 Id)
     where 
           a1 = flipCtx Id
           a2 = flipCtx Id

-- p /\ (q \/ r) |- (p /\ q) \/ (p /\ r) (Proof-term level)
distr1P :: Provable '[p :/\: (q :\/: r)]
                    (Formula ((p :/\: q) :\/: (p :/\: r)))
distr1P = Proof $ \(HCons (AndT p qOrr) HNil) ->
                     case qOrr of
                      OrT1 q -> OrT1 (AndT p q)
                      OrT2 r -> OrT2 (AndT p r)

-- (p /\ q) \/ (p /\ r) |- p /\ (q \/ r) (Proposition level)
distr1'A :: DerivesI '[Formula ((p :/\: q) :\/: (p :/\: r))]
                      (Formula (p :/\: (q :\/: r)))
distr1'A = OrE (AndI (AndE1 Id) (OrI1 (AndE2 Id)))
               (AndI (AndE1 Id) (OrI2 (AndE2 Id)))
               Id

-- (p /\ q) \/ (p /\ r) |- p /\ (q \/ r) (Proof-term level)
distr1'P :: Provable '[(p :/\: q) :\/: (p :/\: r)]
                      (Formula (p :/\: (q :\/: r)))
distr1'P = Proof $ \(HCons x HNil) -> case x of
                          OrT1 (AndT p q) -> AndT p (OrT1 q)
                          OrT2 (AndT p r) -> AndT p (OrT2 r)

-- p \/ (q /\ r) |- (p \/ q) /\ (p \/ r) (Proposition level)
distr2A :: DerivesI '[Formula (p :\/: (q :/\: r))]
                    (Formula ((p :\/: q) :/\: (p :\/: r)))
distr2A = AndI (OrE (OrI1 Id) (OrI2 (AndE1 Id)) Id)
               (OrE (OrI1 Id) (OrI2 (AndE2 Id)) Id)
   
-- p \/ (q /\ r) |- (p \/ q) /\ (p \/ r) (Proof-term level)
distr2P :: Provable '[p :\/: (q :/\: r)]
                    (Formula ((p :\/: q) :/\: (p :\/: r)))
distr2P = Proof $ \(HCons x HNil) -> case x of
                         OrT1 p          -> AndT (OrT1 p) (OrT1 p)
                         OrT2 (AndT q r) -> AndT (OrT2 q) (OrT2 r)
 
-- (p \/ q) /\ (p \/ r) |- p \/ (q /\ r) (Proposition level)
distr2'A :: DerivesI '[Formula ((p :\/: q) :/\: (p :\/: r))]
                      (Formula (p :\/: (q :/\: r)))
distr2'A = OrE (OrI1 Id)
               (OrE (OrI1 Id) (OrI2 (AndI Id (flipCtx Id))) 
                                             (flipCtx (AndE1 Id)))
               (AndE2 Id)
     
-- (p \/ q) /\ (p \/ r) |- p \/ (q /\ r) (Proof-term level)
distr2'P :: Provable '[(p :\/: q) :/\: (p :\/: r)]
                      (Formula (p :\/: (q :/\: r)))
distr2'P = Proof $ \(HCons (AndT pq pr) HNil) -> case (pq, pr) of
                      (OrT1 p, _)      -> OrT1 p
                      (_, OrT1 p)      -> OrT1 p
                      (OrT2 q, OrT2 r) -> OrT2 (AndT q r)

-- p -> (q -> r), p -> q |- p -> r (Proposition level)
impTransA :: DerivesI '[Formula (p :~>: q :~>: r),Formula (p :~>: q)]
                      (Formula (p :~>: r))
impTransA = ImpI (ImpE (ImpE (flipCtx Id) Id)
                      (ImpE (Ex a1 Tr Tr Tr (flipCtx Id)) Id))
           where a1 :: DerivesI '[Formula p] (Formula Top)
                 a1 = Tr
                 
-- p -> (q -> r), p -> q |- p -> r (Proof-term level)
impTransP :: Provable '[p :~>: q :~>: r,p :~>: q]
                       (Formula (p :~>: r))
impTransP = Proof $ \(HCons (ImpT f) (HCons (ImpT g) HNil)) ->
                         ImpT $ \p -> case f p of 
                                   ImpT fp -> fp (g p)

-- p |- ~~p (Proposition level)
doubNegImpA :: DerivesI '[Formula p]
                         (Formula ((p :~>: Bot) :~>: Bot))
doubNegImpA = ImpI (ImpE Id (flipCtx Id))
             
-- p |- ~~p (Proof-term level)
doubNegImpP :: Provable '[p] (Formula ((p :~>: Bot) :~>: Bot))
doubNegImpP = Proof $ \(HCons p HNil) -> ImpT (\(ImpT f) -> f p)

-- ~(p \/ q) |- ~p /\ ~q (Proposition level)
deMorIntA :: DerivesI '[Formula ((p :\/: q) :~>: Bot)]
                       (Formula ((p :~>: Bot) :/\: (q :~>: Bot)))
deMorIntA = AndI (ImpI (ImpE (flipCtx Id) (OrI1 Id)))
                 (ImpI (ImpE (flipCtx Id) (OrI2 Id))) 

-- ~(p \/ q) |- ~p /\ ~q (Proof-term level)
deMorIntP :: Provable '[(p :\/: q) :~>: Bot]
                       (Formula ((p :~>: Bot) :/\: (q :~>: Bot)))
deMorIntP = Proof $ \(HCons (ImpT f) HNil) ->
                      AndT (ImpT (\p -> f (OrT1 p)))
                           (ImpT (\q -> f (OrT2 q)))

-- ~p /\ ~q |- ~(p \/ q) (Proposition level)
deMorInt'A :: DerivesI '[Formula ((p :~>: Bot) :/\: (q :~>: Bot))]
                        (Formula ((p :\/: q) :~>: Bot))
deMorInt'A = ImpI (flipCtx (OrE (ImpE (flipCtx (AndE1 Id)) Id)
                                (ImpE (flipCtx (AndE2 Id)) Id)
                                (flipCtx Id)))

-- ~p /\ ~q |- ~(p \/ q) (Proof-term level)
deMorInt'P :: Provable '[(p :~>: Bot) :/\: (q :~>: Bot)]
                        (Formula ((p :\/: q) :~>: Bot))
deMorInt'P = Proof $ \(HCons (AndT (ImpT f) (ImpT g)) HNil) ->
                      ImpT $ \x -> case x of
                                     OrT1 p -> f p
                                     OrT2 q -> g q

-- ~p \/ q |- p -> q (Proposition level)
orImpA :: DerivesI '[Formula ((p :~>: Bot) :\/: q)]
                    (Formula (p :~>: q))
orImpA = ImpI (flipCtx (OrE
                   (BotE (ImpE Id (Ex a1 Tr Tr Tr (flipCtx Id)))) Id Id))
         where 
                a1 :: DerivesI '[Formula (p :~>: Bot)] (Formula Top)
                a1 = Tr 

-- ~p \/ q |- p -> q (Proof-term level)
orImpP :: Provable '[(p :~>: Bot) :\/: q]
                    (Formula (p :~>: q))
orImpP = Proof $ \(HCons x HNil) -> case x of
                                      OrT1 (ImpT f) -> ImpT (\p -> abort (f p))
                                      OrT2 q        -> ImpT (\_ -> q)

-- |- ((((p -> q) -> p) -> p) -> q) -> q (Proposition level)
wkPeirceA :: DerivesI '[]
                     (Formula (((((p :~>: q) :~>: p) :~>: p) :~>: q) :~>: q))
wkPeirceA = ImpI (ImpE Id
                   (ImpI (ImpE Id
                            (ImpI (ImpE (Ex a0 Tr Tr Tr (flipCtx Id))
                                  (ImpI (flipCtx Id)))))))
           where a0 :: DerivesI '[Formula p] (Formula Top)
                 a0 = Tr

-- |- ((((p -> q) -> p) -> p) -> q) -> q (Proof-term level)
wkPeirceP :: Provable '[]
                     (Formula (((((p :~>: q) :~>: p) :~>: p) :~>: q) :~>: q))
wkPeirceP = Proof $ \HNil -> ImpT
                    (\(ImpT f) -> f (ImpT
                       (\(ImpT g) -> g (ImpT 
                          (\p -> f (ImpT (\_ -> p)))))))
wkPeirceP' :: Provable '[]
                     (Formula (((((p :~>: q) :~>: p) :~>: p) :~>: q) :~>: q))
wkPeirceP' = Proof $ \HNil -> ImpT
                   (\(ImpT f) -> f (ImpT
                        (\(ImpT g) -> g (ImpT (\p -> f (ImpT (\_ -> p)))))))

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

-- |- (((p -> q) -> p) -> p) -> q 
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

-- ~p \/ ~q |- ~(p /\ q)
deMorC' :: DerivesC '[Formula ((p :~>: Bot) :\/: (q :~>: Bot))]
                     (Formula ((p :/\: q) :~>: Bot))
deMorC' = ImpIC (OrEC (ImpEC IdC (flipCtxC (AndE1C IdC)))
                      (ImpEC IdC (flipCtxC (AndE2C IdC)))
                      (flipCtxC IdC))

---------------------------------------------------------------------

    

{-# LANGUAGE FlexibleInstances #-}

module NatDedFun where
       
import Data.Set hiding (map)
import Text.PrettyPrint
import Test.HUnit

data Formula =
      Bot 
    | Var Char
    | And Formula Formula 
    | Or Formula Formula
    | Imp Formula Formula deriving (Eq, Ord, Show)
     
infixl 3 /\
infixl 2 \/ 
infixl 1 ~> 
                  
(/\),(\/),(~>) :: Formula -> Formula -> Formula
(/\) = And
(\/) = Or
(~>) = Imp

data Sequent = Seq {ctxt :: Set Formula,
                    thes :: Formula} deriving (Eq, Show)

isAtomic :: Formula -> Bool
isAtomic  Bot    = True
isAtomic (Var _) = True
isAtomic _       = False

-------------------------------------------------------------------------------
        --Intuitionistic functions
-------------------------------------------------------------------------------

ax :: Formula -> Set Formula -> Maybe Sequent
ax f ctx | member f ctx = Just (Seq ctx f)
         | otherwise    = Nothing
                   
andI :: Sequent -> Sequent -> Maybe Sequent
andI (Seq ctx1 th1) (Seq ctx2 th2) | ctx1 == ctx2 = Just (Seq ctx1 (th1 /\ th2))
                                   | otherwise    = Nothing

andE1 :: Sequent -> Maybe Sequent
andE1 (Seq ctx (And f1 f2)) = Just (Seq ctx f1)
andE1 _                     = Nothing

andE2 :: Sequent -> Maybe Sequent
andE2 (Seq ctx (And f1 f2)) = Just (Seq ctx f2)
andE2 _                     = Nothing

orI1 :: Formula -> Sequent -> Maybe Sequent
orI1 f2 (Seq ctx f1) = Just (Seq ctx (f1 \/ f2))

orI2 :: Formula -> Sequent -> Maybe Sequent
orI2 f1 (Seq ctx f2) = Just (Seq ctx (f1 \/ f2))

orE :: Sequent -> Sequent -> Sequent -> Maybe Sequent
orE (Seq ctx1 th1) (Seq ctx2 th2) (Seq ctx3 (Or f1 f2))
    | member f1 ctx1 && member f2 ctx2
      && th1 == th2 && delete f1 ctx1 == delete f2 ctx2 &&
      delete f1 ctx1 == ctx3          = Just (Seq ctx3 th1)
    | otherwise                       = Nothing
orE _ _ _                             = Nothing

impI :: Formula -> Formula -> Sequent -> Maybe Sequent
impI f1 f2 (Seq ctx f)
        | member f1 ctx && f == f2 = Just (Seq (delete f1 ctx) (f1 ~> f2)) 
        | otherwise                = Nothing

impE :: Sequent -> Sequent -> Maybe Sequent
impE (Seq ctx1 (Imp f1 f2)) (Seq ctx2 f)
     | ctx1 == ctx2 && f1 == f     = Just (Seq ctx1 f2)
     | otherwise                   = Nothing
impE _ _                           = Nothing

botEInt :: Formula -> Sequent -> Maybe Sequent
botEInt f (Seq ctx Bot) = Just (Seq ctx f)
botEInt _ _             = Nothing

------------------------------------------------------------------------
        --Classical function
------------------------------------------------------------------------

botECl :: Formula -> Sequent -> Maybe Sequent
botECl f (Seq ctx Bot)
       | member (f ~> Bot) ctx = Just (Seq (delete (f ~> Bot) ctx) f)
       | otherwise             = Nothing
botECl _ _                     = Nothing 

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

-- p \/ q |- q \/ p (Int)
orFlip :: Formula -> Formula -> Maybe Sequent
orFlip p q = let hyp = singleton (p \/ q) in do
       s1 <- ax p (insert p hyp)
       s2 <- ax q (insert q hyp)
       s3 <- orI2 q s1
       s4 <- orI1 p s2
       s5 <- ax (p \/ q) hyp
       orE s3 s4 s5

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

testInt :: Test
testInt = "Intuitionistic Theorems" ~:
        TestList [ppt (andFlip (Var 'a') (Var 'b')) ~?= "a . b |- b . a",
                  ppt (orFlip (Var 'a') (Var 'b')) ~?= "a + b |- b + a",
                  ppt (distr1 (Var 'a') (Var 'b') (Var 'c'))
                        ~?= "a . (b + c) |- a . b + a . c"]
           where ppt = render . pp
        
                   
                  
class PP a where
   pp :: a -> Doc

maybeParens :: Bool -> Doc -> Doc
maybeParens True = parens
maybeParens False = id
           
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


module NatDedFun where
       
import Data.Set



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

data Sequent = Empty | Seq {ctxt :: Set Formula,
                            thes :: Formula} deriving (Eq, Show)

ax :: Formula -> Set Formula -> Sequent
ax f ctx | member f ctx = Seq ctx f
         | otherwise    = Empty
                                
andI :: Sequent -> Sequent -> Sequent
andI (Seq ctx1 th1) (Seq ctx2 th2) | ctx1 == ctx2 = Seq ctx1 (th1 /\ th2)
                                   | otherwise    = Empty
andI _ _                                          = Empty

andE1 :: Sequent -> Sequent
andE1 (Seq ctx (And f1 f2)) = Seq ctx f1
andE1 _                     = Empty

andE2 :: Sequent -> Sequent
andE2 (Seq ctx (And f1 f2)) = Seq ctx f2
andE2 _                    = Empty

orI1 :: Formula -> Sequent -> Sequent
orI1 f2 (Seq ctx f1) = Seq ctx (f1 \/ f2)
orI1 _ _             = Empty

orI2 :: Formula -> Sequent -> Sequent
orI2 f1 (Seq ctx f2) = Seq ctx (f1 \/ f2)
orI2 _ _             = Empty

orE :: Sequent -> Sequent -> Sequent -> Sequent
orE (Seq ctx1 th1) (Seq ctx2 th2) (Seq ctx3 (Or f1 f2))
    | member f1 ctx1 && member f2 ctx2
      && th1 == th2 && delete f1 ctx1 == delete f2 ctx2 &&
      delete f1 ctx1 == ctx3 = Seq ctx3 th1
    | otherwise = Empty
orE _ _ _       = Empty

impI :: Formula -> Formula -> Sequent -> Sequent
impI f1 f2 (Seq ctx f)
        | member f1 ctx && f == f2 = Seq (delete f1 ctx) (f1 ~> f2) 
        | otherwise                = Empty
impI _ _ _                         = Empty

impE :: Sequent -> Sequent -> Sequent
impE (Seq ctx1 (Imp f1 f2)) (Seq ctx2 f)
     | ctx1 == ctx2 && f1 == f     = Seq ctx1 f2
     | otherwise                   = Empty
impE _ _                           = Empty


-- p /\ q |- q /\ p
andFlip :: Formula -> Formula -> Sequent
andFlip p q = andI (andE2 init) (andE1 init)
        where init = ax (p /\ q) (singleton (p /\ q))

-- p \/ q |- q \/ p
orFlip :: Formula -> Formula -> Sequent
orFlip p q = orE (orI2 q (ax p (insert p hyp)))
                 (orI1 p (ax q (insert q hyp)))
                 (ax (p \/ q) hyp) where hyp = singleton (p \/ q)

-- p -> (q -> r), p -> q, p |- r
tranApp :: Formula -> Formula -> Formula -> Sequent
tranApp p q r = impE (impE (ax (p ~> (q ~> r)) hyp) (ax p hyp))
                (impE (ax (p ~> q) hyp) (ax p hyp)) where
                 hyp = insert (p ~> (q ~> r)) ((insert (p ~> q)) (singleton p))

-- p |- p''
doubleNegImp :: Formula -> Sequent
doubleNegImp p = impI (p ~> Bot) Bot (impE (ax (p ~> Bot) hyp) (ax p hyp)) where 
                 hyp = insert (p ~> Bot) (singleton p)



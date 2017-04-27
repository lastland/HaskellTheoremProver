module NDedFun (Sequent, Pf,
                Formula(Bot, Var, And, Or, Imp),
                ax, wkn,
                andI, andE1, andE2,
                orI1, orI2, orE,
                impI, impE, botEInt, botECl,
                axP, wknP,
                andIP, andEP1, andEP2,
                orIP1, orIP2, orEP,
                impIP, impEP, botEIntP, botEClP,
                (/\), (\/), (~>),
                isAtomic, ctxt, thes) where

import           Data.List (intercalate)
import           Data.Set  hiding (map)
import qualified Data.Set  as Set
import           Data.Tree
import           Proof     (PP, getTree, lift, lift1, lift2, lift3, pp)
import qualified Proof

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

level :: Formula -> Int
level Bot         = 100
level (Var _)     = 100
level (And _ _)   = 8
level (Or _ _)    = 5
level (Imp _ Bot) = 50
level (Imp _ _)   = 2

lp :: (Int -> Int -> Bool) -> Formula -> Formula -> String
lp f x e = (if f (level x) (level e) then parens else id) (pp x)

parens :: String -> String
parens s = "(" ++ s ++ ")"

instance PP Formula where
  pp Bot                 = "⊥"
  pp (Var c)             = [c]
  pp (Imp Bot Bot)       = "~" ++ pp Bot
  pp (Imp e@(Var _) Bot) = "~" ++ pp e
  pp (Imp f Bot)         = "~(" ++ pp f ++ ")"
  pp e@(And f1 f2)       = lp (<=) f1 e ++ " /\\ " ++ lp (<) f2 e
  pp e@(Or  f1 f2)       = lp (<=) f1 e ++ " \\/ " ++ lp (<) f2 e
  pp e@(Imp f1 f2)       = lp (<=) f1 e ++ " ~> " ++ lp (<) f2 e

instance PP Sequent where
  pp (Seq ctx thm) | Set.null ctx = t
                   | otherwise = intercalate ", " (pp <$> toList ctx)
                                 ++ " " ++ t where
                       t =  "|- " ++ pp thm

-------------------------------------------------------------------------------
        --Intuitionistic functions
-------------------------------------------------------------------------------

type Pf = Proof.Proof Maybe Sequent

ax :: Formula -> Set Formula -> Maybe Sequent
ax f ctx | member f ctx = Just (Seq ctx f)
         | otherwise    = Nothing

axP :: Formula -> Set Formula -> Pf
axP f ctx = lift (ax f ctx)

wkn :: Formula -> Sequent -> Maybe Sequent
wkn p (Seq ctx th) = Just (Seq (insert p ctx) th)

wknP :: Formula -> Pf -> Pf
wknP p = lift1 (wkn p)

andI :: Sequent -> Sequent -> Maybe Sequent
andI (Seq ctx1 th1) (Seq ctx2 th2) | ctx1 == ctx2 = Just (Seq ctx1 (th1 /\ th2))
                                   | otherwise    = Nothing

andIP :: Pf -> Pf -> Pf
andIP = lift2 andI

andE1 :: Sequent -> Maybe Sequent
andE1 (Seq ctx (And f1 _)) = Just (Seq ctx f1)
andE1 _                    = Nothing

andEP1 :: Pf -> Pf
andEP1 = lift1 andE1

andE2 :: Sequent -> Maybe Sequent
andE2 (Seq ctx (And _ f2)) = Just (Seq ctx f2)
andE2 _                    = Nothing

andEP2 :: Pf -> Pf
andEP2 = lift1 andE2

orI1 :: Formula -> Sequent -> Maybe Sequent
orI1 f2 (Seq ctx f1) = Just (Seq ctx (f1 \/ f2))

orIP1 :: Formula -> Pf -> Pf
orIP1 = lift1 . orI1

orI2 :: Formula -> Sequent -> Maybe Sequent
orI2 f1 (Seq ctx f2) = Just (Seq ctx (f1 \/ f2))

orIP2 :: Formula -> Pf -> Pf
orIP2 = lift1 . orI2

orE :: Sequent -> Sequent -> Sequent -> Maybe Sequent
orE (Seq ctx1 th1) (Seq ctx2 th2) (Seq ctx3 (Or f1 f2))
    | member f1 ctx1 && member f2 ctx2
      && th1 == th2 && delete f1 ctx1 == delete f2 ctx2 &&
      delete f1 ctx1 == ctx3          = Just (Seq ctx3 th1)
    | otherwise                       = Nothing
orE _ _ _                             = Nothing

orEP :: Pf -> Pf -> Pf -> Pf
orEP = lift3 orE

impI :: Formula -> Sequent -> Maybe Sequent
impI f1 (Seq ctx f)
        | member f1 ctx   = Just (Seq (delete f1 ctx) (f1 ~> f))
        | otherwise       = Nothing

impIP :: Formula -> Pf -> Pf
impIP f1 = lift1 (impI f1)

impE :: Sequent -> Sequent -> Maybe Sequent
impE (Seq ctx1 (Imp f1 f2)) (Seq ctx2 f)
     | ctx1 == ctx2 && f1 == f     = Just (Seq ctx1 f2)
     | otherwise                   = Nothing
impE _ _                           = Nothing

impEP :: Pf -> Pf -> Pf
impEP = lift2 impE

botEInt :: Formula -> Sequent -> Maybe Sequent
botEInt f (Seq ctx Bot) = Just (Seq ctx f)
botEInt _ _             = Nothing

botEIntP :: Formula -> Pf -> Pf
botEIntP = lift1 . botEInt

------------------------------------------------------------------------
        --Classical function
------------------------------------------------------------------------

botECl :: Formula -> Sequent -> Maybe Sequent
botECl f (Seq ctx Bot)
       | member (f ~> Bot) ctx = Just (Seq (delete (f ~> Bot) ctx) f)
       | otherwise             = Nothing
botECl _ _                     = Nothing

botEClP :: Formula -> Pf -> Pf
botEClP = lift1 . botECl

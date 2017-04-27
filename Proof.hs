module Proof where

import           Data.Tree
import           ProofTree

class PP a where
   pp :: a -> String

newtype Proof m a = P { prove :: m (a, ProofTree) }

getTree :: (Monad m) => Proof m a -> m ProofTree
getTree p = snd <$> prove p

lift :: (Monad m, PP a) => m a -> Proof m a
lift a = P $ do t <- a
                return (t, Node (pp t) [])

lift1 :: (Monad m, PP b) => (a -> m b) -> Proof m a -> Proof m b
lift1 f a = P $ do (t, p) <- prove a
                   t' <- f t
                   return (t', Node (pp t') [p])

lift2 :: (Monad m, PP c) => (a -> b -> m c) ->
  Proof m a -> Proof m b -> Proof m c
lift2 f a b = P $ do (ta, pa) <- prove a
                     (tb, pb) <- prove b
                     t <- f ta tb
                     return (t, Node (pp t) [pa, pb])

lift3 :: (Monad m, PP d) => (a -> b -> c -> m d) ->
  Proof m a -> Proof m b -> Proof m c -> Proof m d
lift3 f a b c = P $ do (ta, pa) <- prove a
                       (tb, pb) <- prove b
                       (tc, pc) <- prove c
                       t <- f ta tb tc
                       return (t, Node (pp t) [pa, pb, pc])

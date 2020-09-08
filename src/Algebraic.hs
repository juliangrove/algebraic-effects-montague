{-# LANGUAGE
    AllowAmbiguousTypes,
    DataKinds,
    FlexibleContexts,
    FlexibleInstances,
    GADTs,
    InstanceSigs,
    MultiParamTypeClasses,
    RankNTypes,
    TypeApplications,
    TypeFamilies,
    TypeOperators #-}

module Algebraic where

import Prelude hiding (Monad(..))
import Control.Effect
import Data.Type.Set ((:++))
import Model

-- | The data type of effectful computations.
data F p v where
  Pure :: (forall o . (v -> o) -> o) -> F '[] v
  Effect :: (forall o . (e -> (a -> F p v) -> o) -> o)
         -> F ((e -> a) ': p) v

-- | Computations with algebraic effects form a graded monad.        
instance Effect F where
  type Unit F = '[]
  type Plus F p q = p :++ q

  return :: v -> F '[] v
  return a = Pure $ \k -> k a

  (>>=) :: F p v -> (v -> F q w) -> F (p :++ q) w
  Pure m >>= k = m k
  Effect m >>= k = Effect $ \h -> m $ \e k' -> h e (\x -> k' x >>= k)

join :: F p (F q v) -> F (p :++ q) v
join m = m >>= id

instance Functor (F p) where
  fmap f (Pure m) = Pure $ \k -> m (k . f)
  fmap f (Effect m) = Effect $ \h -> m $ \e k -> h e (\x -> fmap f $ k x)


-- =====================
-- == Effect handling ==
-- =====================

-- | The class of handleable effects. Handle a list of effects p to turn it into
-- a list of effects q, by using some collection of handlers.
class Handleable handlers p q where
  handle :: handlers -> F p v -> F q v

-- | Handling a pure computation just returns it.
instance Handleable handlers '[] '[] where
  handle hndlrs m = m

-- | Handle a 'choose'.
instance Handleable ([Entity] -> Entity, () -> [Entity]) p q
      => Handleable ([Entity] -> Entity, () -> [Entity])
                    (([Entity] ->  Entity) ': p) q where
  handle hndlrs (Effect m) = m $ \x k -> handle hndlrs $ k $ fst hndlrs x

-- | Handle a 'get'.
instance Handleable ([Entity] -> Entity, () -> [Entity]) p q
      => Handleable ([Entity] -> Entity, () -> [Entity])
                    ((() -> [Entity]) ': p) q where
  handle hndlrs (Effect m) = m $ \_ k -> handle hndlrs $ k $ snd hndlrs ()

-- | Handle a 'put'.
instance Handleable ([Entity] -> Entity, () -> [Entity]) p q
      => Handleable ([Entity] -> Entity, () -> [Entity])
                    (([Entity] -> ()) ': p) q where
  handle hndlrs (Effect m) = m $ \g k -> handle (fst hndlrs, (\() -> g)) $ k ()

-- =====================
-- == Non-determinism ==
-- =====================

choose :: [Entity] -> (Entity -> F p v) -> F (([Entity] -> Entity) ': p) v
choose p k = Effect $ \h -> h p k

choose' :: [Entity] -> F '[[Entity] -> Entity] Entity
choose' p = choose p return


-- ===========
-- == State ==
-- ===========

get :: () -> ([Entity] -> F p v) -> F ((() -> [Entity]) ': p) v
get () k = Effect $ \h -> h () k

put :: [Entity] -> (() -> F p v) -> F (([Entity] -> ()) ': p) v
put g k = Effect $ \h -> h g k

get' :: () -> F '[() -> [Entity]] [Entity]
get' () = get () return

put' :: [Entity] -> F '[[Entity] -> ()] ()
put' g = put g return


-- =============
-- == Lexicon ==
-- =============

(|>) :: F p (a -> b) -> F q a -> F (p :++ q) b
m |> n = join $ fmap (\f -> fmap (\x -> f x) n) m

(<|) :: F p a -> F q (a -> b) -> F (p :++ q) b
m <| n = join $ fmap (\x -> fmap (\f -> f x) n) m

some :: (Entity -> Bool) -> F '[[Entity] -> Entity] Entity
some pred = choose' (filter pred entities)

bind :: F p Entity -> F (p :++ [() -> [Entity], [Entity] -> ()]) Entity
bind m = m >>= \x -> get' () >>= \g -> put' (x:g) >>= \() -> return x

itself :: F '[() -> [Entity]] Entity
itself = fmap head $ get'()

-- ==============
-- == Examples ==
-- ==============

-- | sentence1: Some squid ate some octopus.
sentence1 = some squid <| (return ate |> (some octopus))

-- | sentence2: Some squid ate itself.
sentence2 = bind (some squid) <| (return ate |> itself)

-- ===========
-- == Misc. ==
-- ===========

-- | Handle a sentence with effects.
handleSentence :: Handleable ([Entity] -> Entity, () -> [Entity]) p '[]
               => F p Bool -> F '[] Bool
handleSentence = (handle @([Entity] -> Entity, () -> [Entity])) (head, const [])

-- | Retrieve the value of a computation with no effects.                 
getVal :: F '[] v -> v
getVal (Pure m) = m id

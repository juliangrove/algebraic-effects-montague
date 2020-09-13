{-# LANGUAGE
    DataKinds,
    FlexibleContexts,
    FlexibleInstances,
    GADTs,
    InstanceSigs,
    MultiParamTypeClasses,
    RankNTypes,
    TypeApplications,
    TypeFamilies,
    TypeOperators,
    UnicodeSyntax #-}

module Algebraic where

import Prelude hiding (Monad(..))
import Control.Effect
import Data.Type.Set ((:++))
import Model

-- | The data type of effectful computations.
data F p v where
  Pure :: v → F '[] v
  Impure :: (∀o. (e → (a → F p v) → o) → o) → F ((e → a) ': p) v

-- | Computations with algebraic effects form a graded monad.        
instance Effect F where
  type Unit F = '[]
  type Plus F p q = p :++ q
  
  return :: v → F '[] v
  return = Pure

  (>>=) :: F p v → (v → F q w) → F (p :++ q) w
  Pure v >>= k = k v
  Impure m >>= k = Impure $ \h → m $ \p k' → h p (\a → k' a >>= k)

join :: F p (F q v) → F (p :++ q) v
join m = m >>= id

instance Functor (F p) where
  fmap f (Pure v) = Pure $ f v
  fmap f (Impure m) = Impure $ \h → m $ \e k → h e (\x → fmap f $ k x)


-- =====================
-- == Non-determinism ==
-- =====================

choose :: [Entity] → (Entity → F p v) → F (([Entity] → Entity) ': p) v
choose p k = Impure $ \h → h p k

choose' :: [Entity] → F '[[Entity] → Entity] Entity
choose' p = choose p return


-- ===========
-- == State ==
-- ===========

get :: () → ([Entity] → F p v) → F ((() → [Entity]) ': p) v
get () k = Impure $ \h → h () k

put :: [Entity] → (() → F p v) → F (([Entity] → ()) ': p) v
put g k = Impure $ \h → h g k

get' :: () → F '[() → [Entity]] [Entity]
get' () = get () return

put' :: [Entity] → F '[[Entity] → ()] ()
put' g = put g return


-- ====================
-- == Quantification ==
-- ====================

type Quantifier = (Entity → Bool) → Bool

quant :: Quantifier → (Entity → F p v) → F ((Quantifier → Entity) ': p) v
quant q k = Impure $ \h → h q k

quant' :: Quantifier → F '[Quantifier → Entity] Entity
quant' q = quant q return


-- =====================
-- == Effect handling ==
-- =====================

-- | The class of handleable effects. Handle a list of effects p associated with
-- some value v to turn it into a list of effects q, by using some collection of
-- handlers.
class Handleable handlers p q v where
  handle :: handlers → F p v → F q v

-- | Handling a pure computation just returns it.
instance Handleable handlers '[] '[] v where
  handle hndlrs m = m

-- | Quantifiers may only be handled when the value type is @Bool@.
instance Handleable handlers p '[] Bool
       ⇒ Handleable handlers ((Quantifier → Entity) ': p) '[] Bool where
  handle handlers (Impure m)
    = Pure $ m $ \q k → q $ \x → getVal $ handle handlers $ k x

-- | Handle a 'choose'.
instance Handleable ([Entity] → Entity, () → [Entity]) p q v
       ⇒ Handleable ([Entity] → Entity, () → [Entity])
                    (([Entity] →  Entity) ': p) q v where
  handle hndlrs (Impure m) = m $ \p k → handle hndlrs $ k $ fst hndlrs p

-- | Handle a 'get'.
instance Handleable ([Entity] → Entity, () → [Entity]) p q v
       ⇒ Handleable ([Entity] → Entity, () → [Entity])
                    ((() → [Entity]) ': p) q v where
  handle hndlrs (Impure m) = m $ \() k → handle hndlrs $ k $ snd hndlrs ()

-- | Handle a 'put'.
instance Handleable ([Entity] → Entity, () → [Entity]) p q v
       ⇒ Handleable ([Entity] → Entity, () → [Entity])
                    (([Entity] → ()) ': p) q v where
  handle hndlrs (Impure m) = m $ \g k → handle (fst hndlrs, (\() → g)) $ k ()


-- =============
-- == Lexicon ==
-- =============

(▹) :: F p (a → b) → F q a → F (p :++ q) b
m ▹ n = join $ fmap (\f → fmap (\x → f x) n) m

(◃) :: F p a → F q (a → b) → F (p :++ q) b
m ◃ n = join $ fmap (\x → fmap (\f → f x) n) m

every :: (Entity → Bool) → F '[Quantifier → Entity] Entity
every pred = quant' (\scope → all scope $ filter pred entities)

some :: (Entity → Bool) → F '[[Entity] → Entity] Entity
some pred = choose' (filter pred entities)

-- | /some/ as a quantifier
someQ :: (Entity → Bool) → F '[Quantifier → Entity] Entity
someQ pred = quant' (\scope → any scope $ filter pred entities)

bind :: F p Entity → F (p :++ [() → [Entity], [Entity] → ()]) Entity
bind m = m >>= \x → get' () >>= \g → put' (x:g) >>= \() → return x

itself :: F '[() → [Entity]] Entity
itself = fmap head $ get' ()


-- ==============
-- == Examples ==
-- ==============

-- | sentence1: Some squid ate some octopus.
sentence1 = some squid ◃ (return ate ▹ some octopus)

-- | sentence2: Some squid ate itself.
sentence2 = bind (some squid) ◃ (return ate ▹ itself)

-- | sentence3: Every octopus ate itself.
sentence3 = bind (every octopus) ◃ (return ate ▹ itself)

-- | sentence4: Some squid ate some octopus. (A sentence with 'someQ'.)
sentence4 = someQ crab ◃ (return sipped ▹ someQ (iced latte))


-- ===========
-- == Misc. ==
-- ===========

-- | Handle a sentence with effects.
handleSentence :: Handleable ([Entity] → Entity, () → [Entity]) p '[] Bool
               ⇒ F p Bool → F '[] Bool
handleSentence = (handle @([Entity] → Entity, () → [Entity])) (head, const [])

-- | Retrieve the value of a computation with no effects.                 
getVal :: F '[] v → v
getVal (Pure v) = v

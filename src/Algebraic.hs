{-# LANGUAGE
    DataKinds,
    FlexibleContexts,
    FlexibleInstances,
    GADTs,
    InstanceSigs,
    MultiParamTypeClasses,
    RankNTypes,
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


-- ================
-- == Operations ==
-- ================

-- | The type of an operation taking parameter p and a-many arguments.
type Operation p a = ∀l v. p → (a → F l v) → F ((p → a) ': l) v

-- | Operations take a parameter, p, and a-many arguments. Handlers then use the
-- parameter to choose which arguments they will further handle.
op :: Operation p a
op p k = Impure $ \h → h p k

-- | The type of a computation consisting of a single operation.
type Computation p a = p → F '[p → a] a

-- | Computations (of one operation) just perform the operation and return the
-- result.
comp :: Computation p a
comp p = op p return


-- ===========
-- == State ==
-- ===========

get :: Operation () [Entity]
get = op

put :: Operation [Entity] ()
put = op

get' :: Computation () [Entity]
get' = comp

put' :: Computation [Entity] ()
put' = comp


-- ====================
-- == Quantification ==
-- ====================

type Quantifier = (Entity → Bool) → Bool

quant :: Operation Quantifier Entity
quant = op

quant' :: Computation Quantifier Entity
quant' = comp


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

-- | Handle a 'get'.
instance Handleable (() → [Entity]) p q v
       ⇒ Handleable (() → [Entity])
                    ((() → [Entity]) ': p) q v where
  handle hndlrs (Impure m) = m $ \() k → handle hndlrs $ k $ hndlrs ()

-- | Handle a 'put'.
instance Handleable (() → [Entity]) p q v
       ⇒ Handleable (() → [Entity])
                    (([Entity] → ()) ': p) q v where
  handle hndlrs (Impure m) = m $ \g k → handle (\() → g) $ k ()


-- ===========
-- == Misc. ==
-- ===========

-- | Retrieve the value of a computation with no effects.                 
getVal :: F '[] v → v
getVal (Pure v) = v

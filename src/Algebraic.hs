{-# LANGUAGE
    DataKinds,
    FlexibleContexts,
    FlexibleInstances,
    GADTs,
    InstanceSigs,
    MultiParamTypeClasses,
    RankNTypes,
    TypeFamilies,
    TypeOperators #-}

module Algebraic where

import Prelude hiding (Monad(..))
import Control.Effect
import Data.Type.Set ((:++))
import Model

data a >-- b

-- | The data type of effectful computations.
data F l v where
  Pure :: v -> F '[] v
  Impure :: (forall o . (e -> (a -> F l v) -> o) -> o) -> F ((e >-- a) ': l) v

-- | Computations with algebraic effects form a graded monad.        
instance Effect F where
  type Unit F = '[]
  type Plus F l1 l2 = l1 :++ l2
  
  return :: v -> F '[] v
  return = Pure

  (>>=) :: F l1 v -> (v -> F l2 w) -> F (l1 :++ l2) w
  Pure v >>= k = k v
  Impure m >>= k = Impure $ \h -> m $ \p k' -> h p (\a -> k' a >>= k)

join :: F l1 (F l2 v) -> F (l1 :++ l2) v
join m = m >>= id

instance Functor (F l) where
  fmap f (Pure v) = Pure $ f v
  fmap f (Impure m) = Impure $ \h -> m $ \e k -> h e (\x -> fmap f $ k x)


-- ================
-- == Operations ==
-- ================

-- | The type of an operation taking parameter p and a-many arguments.
type Operation p a = forall l v . p -> (a -> F l v) -> F ((p >-- a) ': l) v

-- | Operations take a parameter, p, and a-many arguments. Handlers then use the
-- parameter to choose which arguments they will further handle.
op :: Operation p a
op p k = Impure $ \h -> h p k

-- | The type of a computation consisting of a single operation.
type Computation p a = p -> F '[p >-- a] a

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

type Quantifier = (Entity -> Bool) -> Bool

scope :: Operation Quantifier Entity
scope = op

scope' :: Computation Quantifier Entity
scope' = comp


-- =====================
-- == Effect handling ==
-- =====================

-- | The class of handleable effects. Handle a list of effects l1 associated
-- with some value v to turn it into a list of effects l2, by using some
-- collection of handlers.
class Handleable handlers l1 l2 v where
  handle :: handlers -> F l1 v -> F l2 v

-- | Handling a pure computation just returns it.
instance Handleable handlers '[] '[] v where
  handle hndlrs m = m

-- | Quantifiers may only be handled when the value type is @Bool@.
instance Handleable handlers l '[] Bool
      => Handleable handlers ((Quantifier >-- Entity) ': l) '[] Bool where
  handle handlers (Impure m)
    = Pure $ m $ \q k -> q $ \x -> getVal $ handle handlers $ k x

-- | Handle a 'get'.
instance Handleable (() -> [Entity]) l1 l2 v
      => Handleable (() -> [Entity]) ((() >-- [Entity]) ': l1) l2 v where
  handle hndlrs (Impure m) = m $ \() k -> handle hndlrs $ k $ hndlrs ()

-- | Handle a 'put'.
instance Handleable (() -> [Entity]) l1 l2 v
      => Handleable (() -> [Entity]) (([Entity] >-- ()) ': l1) l2 v where
  handle hndlrs (Impure m) = m $ \g k -> handle (\() -> g) $ k ()


-- ===========
-- == Misc. ==
-- ===========

-- | Retrieve the value of a computation with no effects. Similar to Maršík's
-- "cherry".
getVal :: F '[] v -> v
getVal (Pure v) = v

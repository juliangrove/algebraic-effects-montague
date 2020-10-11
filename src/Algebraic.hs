{-# LANGUAGE
    DataKinds,
    FlexibleInstances,
    GADTs,
    InstanceSigs,
    MultiParamTypeClasses,
    RankNTypes,
    ScopedTypeVariables,
    TypeApplications,
    TypeFamilies,
    TypeOperators,
    UndecidableInstances #-}

module Algebraic where

import Prelude hiding (Monad(..))
import qualified Control.Monad.State as CMS
import Control.Effect
import Data.Functor.Identity
import Data.Type.Set ((:++))
import Model

data a >-- b

-- | The data type of effectful computations.
data F l v where
  Pure :: v -> F '[] v
  Impure :: (forall o . (p -> (a -> F l v) -> o) -> o) -> F ((p >-- a) ': l) v

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

-- | The class of handlers whose individual interpreters may be retrieved.
class Retrievable interpreter handler where
  retrieve :: handler -> interpreter

-- | A type for value handlers.
type HandleVal l v1 v2 = v1 -> F l v2

-- | A type for operation handlers.
type HandlerOf p a l v = p -> (a -> F l v) -> F l v

type StateHandler p a v = HandlerOf p a '[() >-- [Entity], [Entity] >-- ()] v
type HandleStateVal v = HandleVal '[() >-- [Entity], [Entity] >-- ()] v v
type HandleGet v = StateHandler () [Entity] v
type HandlePut v = StateHandler [Entity] () v
type HandleScope = StateHandler Quantifier Entity Bool

-- | Interpret a 'get' occurrence.
handleGet :: HandleGet v
handleGet
  = \_ k -> Impure $ \h -> h () $ \g -> case k g of
                                          Impure m -> m $ \_ k' -> k' g

-- | Interpret a 'put' occurrence.
handlePut :: HandlePut v
handlePut
  = \g k -> Impure $ \h -> h () $ \_ -> case k () of
                                          Impure m -> m $ \_ k' -> k' g

-- | Interpret a 'scope' occurrence.
handleScope :: HandleScope
handleScope
  = \q k ->
  Impure $ \h -> h () $ \g ->
  Impure $ \h' -> h' g $ \_ ->
  Pure $ q $ \x -> case k x of
                     Impure m -> m $ \_ k' ->
                       case k' g of
                         Impure m' -> m' $ \_ k'' ->
                           case k'' () of
                             Pure a -> a

-- | Interpret a value.
handleVal :: HandleStateVal v
handleVal
  = \v -> Impure $ \h -> h () $ \g -> Impure $ \h' -> h' g $ \_ -> Pure v

-- | The type of handlers for computations possibly featuring 'get', 'put', and
-- 'scope'.
type GetPutScopeHandler
  = (HandleGet Bool, (HandlePut Bool, (HandleScope, HandleStateVal Bool)))
                                                    
-- | A handler for computations possibly featuring 'get', 'put', and 'scope'.
getPutScopeHandler :: GetPutScopeHandler
getPutScopeHandler = (handleGet, (handlePut, (handleScope, handleVal)))

-- | When a handler has only one component.
instance Retrievable interpreter interpreter where
  retrieve = id

-- | Access the first component of a handler.
instance Retrievable interpreter (interpreter, handler) where
  retrieve = fst

-- | Look past the first component to retrieve an interpreter from inside the
-- second component.
instance Retrievable (HandleStateVal v) handler
      => Retrievable (HandleStateVal v) (HandleGet v, handler) where
  retrieve = retrieve . snd

-- | Look past the first component to retrieve a handler from inside the
-- second component.
instance Retrievable (HandleStateVal v) handler
      => Retrievable (HandleStateVal v) (HandlePut v, handler) where
  retrieve = retrieve . snd

-- | Look past the first component to retrieve a handler from inside the
-- second component.
instance Retrievable (HandleStateVal v) handler
      => Retrievable (HandleStateVal v) (HandleScope, handler) where
  retrieve = retrieve . snd

-- | Look past the first component to retrieve a handler from inside the
-- second component.
instance Retrievable (HandleGet v) handler
      => Retrievable (HandleGet v) (HandlePut v, handler) where
  retrieve = retrieve . snd

-- | Look past the first component to retrieve a handler from inside the
-- second component.
instance Retrievable (HandleGet v) handler
      => Retrievable (HandleGet v) (HandleScope, handler) where
  retrieve = retrieve . snd

-- | Look past the first component to retrieve a handler from inside the
-- second component.
instance Retrievable (HandlePut v) handler
      => Retrievable (HandlePut v) (HandleGet v, handler) where
  retrieve = retrieve . snd

-- | Look past the first component to retrieve a handler from inside the
-- second component.
instance Retrievable (HandlePut v) handler
      => Retrievable (HandlePut v) (HandleScope, handler) where
  retrieve = retrieve . snd

-- | Look past the first component to retrieve a handler from inside the
-- second component.
instance Retrievable HandleScope handler
      => Retrievable HandleScope (HandleGet v, handler) where
  retrieve = retrieve . snd

-- | Look past the first component to retrieve a handler from inside the
-- second component.
instance Retrievable HandleScope handler
      => Retrievable HandleScope (HandlePut v, handler) where
  retrieve = retrieve . snd

-- | The class of handleable effects. Handle a computation associated with the
-- list of effects l1 and value type v1 to turn it into a computation associated
-- with the list of effects l2 and value type v2, in a way that depends on the
-- given handler.
class Handleable handler l1 l2 v1 v2 where
  handle :: handler -> F l1 v1 -> F l2 v2

-- | Handle a value.
instance Retrievable (HandleStateVal v) handler
      => Handleable handler '[] '[() >-- [Entity], [Entity] >-- ()] v v where
  handle handler (Pure v) = retrieve handler v

-- | Handle an operation.
instance (Retrievable (StateHandler p a v) handler,
          Handleable handler l '[() >-- [Entity], [Entity] >-- ()] v v)
      => Handleable handler (p >-- a ': l)
         '[() >-- [Entity], [Entity] >-- ()] v v where
  handle handler (Impure m)
    = m $ \p k -> retrieve @(StateHandler p a v)
                  handler p (\a -> handle handler (k a))


-- ===========
-- == Misc. ==
-- ===========

-- | Retrieve the value of a computation with no effects. Similar to Maršík's
-- "cherry".
getVal :: F '[] v -> v
getVal (Pure v) = v

-- | Evalutate a computation with one 'get' and one 'put' into the State monad.
evalState :: F '[() >-- [Entity], [Entity] >-- ()] v -> CMS.State [Entity] v
evalState (Impure m) = CMS.StateT $ \g -> m $ \_ k -> case k g of
                                           Impure m' -> m' $ \g' k' ->
                                             case k' () of
                                               Pure v -> Identity (v, g')

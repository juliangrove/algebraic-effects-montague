{-# LANGUAGE
    AllowAmbiguousTypes,
    ConstraintKinds,
    DataKinds,
    FlexibleContexts,
    FlexibleInstances,
    FunctionalDependencies,
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

-- | The class of handlers whose components may be retrieved.
class Member handler handlers where
  getHandler :: handlers -> handler


-- | A type for value handlers.
type HandleVal v1 v2 = v1 -> F '[] v2
-- | A type for operation handlers.
type HandlerOf p a v = p -> (a -> F '[] v) -> F '[] v

type HandleGet v = HandlerOf () [Entity] ([Entity] -> v)
type HandlePut v = HandlerOf [Entity] () ([Entity] -> v)
type HandleScope = HandlerOf Quantifier Entity ([Entity] -> Bool)

-- | The type of handlers for computations possibly featuring 'get', 'put', and
-- 'scope'.
type GetPutScopeHandler = (HandleGet Bool,
                           (HandlePut Bool,
                            (HandleScope,
                             HandleVal Bool ([Entity] -> Bool))))
                          
-- | A handler for computations possibly featuring 'get', 'put', and 'scope'.
getPutScopeHandler :: GetPutScopeHandler
getPutScopeHandler = (\_ k -> Pure $ \g -> let Pure f = k g in f g,
                      (\g k -> Pure $ \_ -> let Pure f = k () in f g,
                       (\q k -> Pure $ \g -> q $ \x -> let Pure f = k x in f g,
                        Pure . const)))

-- | When the handlers have only one component.
instance Member handler handler where
  getHandler = id

-- | Access the first component of a collection of handlers.
instance Member handler (handler, handlers) where
  getHandler = fst

-- | Look past the first component to retrieve a handler from the inside the
-- second component.
instance Member (HandleVal v ([Entity] -> v)) handlers
      => Member (HandleVal v ([Entity] -> v)) (HandleGet v, handlers) where
  getHandler = getHandler . snd

-- | Look past the first component to retrieve a handler from the inside the
-- second component.
instance Member (HandleVal v ([Entity] -> v)) handlers
      => Member (HandleVal v ([Entity] -> v)) (HandlePut v, handlers) where
  getHandler = getHandler . snd

-- | Look past the first component to retrieve a handler from the inside the
-- second component.
instance Member (HandleVal v ([Entity] -> v)) handlers
      => Member (HandleVal v ([Entity] -> v)) (HandleScope, handlers) where
  getHandler = getHandler . snd

-- | Look past the first component to retrieve a handler from the inside the
-- second component.
instance Member (HandleGet v) handlers
      => Member (HandleGet v)
                (HandlePut v, handlers) where
  getHandler = getHandler . snd

-- | Look past the first component to retrieve a handler from the inside the
-- second component.
instance Member (HandleGet v) handlers
      => Member (HandleGet v) (HandleScope, handlers) where
  getHandler = getHandler . snd

-- | Look past the first component to retrieve a handler from the inside the
-- second component.
instance Member (HandlePut v) handlers
      => Member (HandlePut v) (HandleGet v, handlers) where
  getHandler = getHandler . snd

-- | Look past the first component to retrieve a handler from the inside the
-- second component.
instance Member (HandlePut v) handlers
      => Member (HandlePut v) (HandleScope, handlers) where
  getHandler = getHandler . snd

-- | Look past the first component to retrieve a handler from the inside the
-- second component.
instance Member HandleScope handlers
      => Member HandleScope (HandleGet v, handlers) where
  getHandler = getHandler . snd

-- | Look past the first component to retrieve a handler from the inside the
-- second component.
instance Member HandleScope handlers
      => Member HandleScope (HandlePut v, handlers) where
  getHandler = getHandler . snd

-- | The class of handleable effects. Handle a computation associated with the
-- list of effects l1 and value type v1 to turn it into a computation with list
-- of effects l2 and value type v2, in a way that depends on the given handler.
class Handleable handlers l1 l2 v1 v2 where
  handle :: handlers -> F l1 v1 -> F l2 v2

-- | Handle a value.
instance Member (HandleVal v ([Entity] -> v)) handlers
      => Handleable handlers '[] '[] v ([Entity] -> v) where
  handle hndlrs (Pure v) = getHandler hndlrs v

-- | Handle an operation.
instance (Member (HandlerOf p a ([Entity] -> v)) handlers,
          Handleable handlers l '[] v ([Entity] -> v))
      => Handleable handlers (p >-- a ': l) '[] v ([Entity] -> v) where
  handle hndlrs (Impure m)
    = m $ \p k -> getHandler @(HandlerOf p a ([Entity] -> v))
                  hndlrs p (\a -> handle hndlrs (k a))


-- ===========
-- == Misc. ==
-- ===========

-- | Retrieve the value of a computation with no effects. Similar to Maršík's
-- "cherry".
getVal :: F '[] v -> v
getVal (Pure v) = v

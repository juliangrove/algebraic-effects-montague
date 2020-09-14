{-# LANGUAGE
    DataKinds,
    InstanceSigs,
    TypeOperators,
    UnicodeSyntax #-}

module Parameterized where

import Prelude hiding (Monad (..))
import qualified Control.Effect as E
import Control.Effect.Parameterised
import Data.Type.Set((:++))
import Algebraic

newtype H l2 l1 v = H { runH :: (v -> F l1 Bool) -> F l2 Bool }

instance PMonad H where
  return :: v -> H l l v
  return v = H $ \k -> k v

  (>>=) :: H l3 l2 v -> (v -> H l2 l1 w) -> H l3 l1 w
  m >>= k = H $ \k' -> runH m $ \x -> runH (k x) k'

liftF :: F l1 v -> H (l1 :++ l2) l2 v
liftF m = H $ \k -> m E.>>= k

lowerH :: H l '[] Bool -> F l Bool
lowerH m = runH m E.return

join :: H l3 l2 (H l2 l1 v) → H l3 l1 v
join m = m >>= id

instance Functor (H l2 l1) where
  fmap f (H m) = H $ \k -> m $ k . f

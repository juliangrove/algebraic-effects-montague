{-# LANGUAGE
    DataKinds,
    FlexibleContexts,
    TypeOperators #-}

module Fragment where

import Prelude hiding (Monad(..))
import qualified Control.Monad.State as CMS
import Control.Effect
import Data.Type.Set((:++))
import Algebraic
import Model

-- =============
-- == Lexicon ==
-- =============

-- | Forward application
(|>) :: F l1 (v -> w) -> F l2 v -> F (l1 :++ l2) w
m |> n = join $ fmap (\f -> fmap (\x -> f x) n) m

-- | Backward application
(<|) :: F l1 v -> F l2 (v -> w) -> F (l1 :++ l2) w
m <| n = join $ fmap (\x -> fmap (\f -> f x) n) m

every :: (Entity -> Bool) -> F '[Quantifier >-- Entity] Entity
every pred = scope' (\scope -> all scope $ filter pred entities)

some :: (Entity -> Bool) -> F '[Quantifier >-- Entity] Entity
some pred = scope' (\scope -> any scope $ filter pred entities)

-- | Make a computation returning an 'Entity' live for anaphora.
bind :: F l Entity -> F (l :++ [() >-- [Entity], [Entity] >-- ()]) Entity
bind m = m >>= \x ->
         get' () >>= \g ->
         put' (x:g) >>
         return x

itself :: F '[() >-- [Entity]] Entity
itself = fmap head $ get' ()


-- ==============
-- == Examples ==
-- ==============

-- | sentence1: Some squid ate some octopus.
sentence1 = some squid <| (return ate |> some octopus)

-- | sentence2: Some squid ate itself.
sentence2 = bind (some squid) <| (return ate |> itself)

-- | sentence3: Every octopus ate itself
sentence3 = bind (every octopus) <| (return ate |> itself)

-- | sentence4: Some crab sipped some iced latte.
sentence4 = some crab <| (return sipped |> some (iced latte))

-- | sentence5: Ashley ate itself.
sentence5 = bind (return ashley) <| (return ate |> itself)

-- ===========
-- == Misc. ==
-- ===========

-- | Handle a sentence with effects, using a 'GetPutScopeHandler'.
handleSentence :: Handleable GetPutScopeHandler l
                  '[() >-- [Entity], [Entity] >-- ()] Bool Bool
               => F l Bool -> F '[() >-- [Entity], [Entity] >-- ()] Bool
handleSentence = handle getPutScopeHandler

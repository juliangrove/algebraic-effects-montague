{-# LANGUAGE
    DataKinds,
    FlexibleContexts,
    MonoLocalBinds,
    TypeApplications,
    TypeOperators #-}

module Fragment where

import Prelude hiding (Monad(..))
import qualified Control.Effect as E
import Control.Effect.Parameterised
import Data.Type.Set((:++))
import Algebraic as A
import Parameterized as P
import Model

-- =============
-- == Lexicon ==
-- =============

(|>) :: H l3 l2 (v -> w) -> H l2 l1 v -> H l3 l1 w
m |> n = P.join $ fmap (\f -> fmap (\x -> f x) n) m

(<|) :: H l3 l2 v -> H l2 l1 (v -> w) -> H l3 l1 w
m <| n = P.join $ fmap (\x -> fmap (\f -> f x) n) m

every1 :: (Entity -> Bool) -> F '[Quantifier >-- Entity] Entity
every1 pred = scope' (\scope -> all scope $ filter pred entities)

some :: (Entity -> Bool) -> F '[Quantifier >-- Entity] Entity
some pred = scope' (\scope -> any scope $ filter pred entities)

bind :: H l2 ((() >-- [Entity]) : ([Entity] >-- ()) : l1) Entity
     -> H l2 l1 Entity
bind m = m >>= \x ->
         liftF (get' ()) >>= \g ->
         liftF (put' (x:g)) >>= \() ->
         return x

itself :: F '[() >-- [Entity]] Entity
itself = fmap head $ get' ()

every2 :: (Handleable GetPutScopeHandler l '[] Bool ([Entity] -> Bool))
       => (Entity -> Bool) -> H '[] l Entity
every2 pred = H $ \k -> Pure $ all (\x -> flip getVal [] $ handleSentence (k x))
                        $ filter pred entities


-- ==============
-- == Examples ==
-- ==============

-- | sentence1: Some squid ate some octopus.
sentence1 = liftF (some squid) <| (return ate |> liftF (some octopus))

-- | sentence2: Some squid ate itself.
sentence2 = bind (liftF (some squid)) <| (return ate |> liftF itself)

-- | sentence3: Every octopus ate itself.
sentence3 = bind (liftF (every1 octopus)) <| (return ate |> liftF itself)

-- | sentence3': Every octopus ate itself.
sentence3' :: F '[] Bool
sentence3' = lowerH $ bind (every2 octopus) <| (return ate |> liftF itself)

-- | sentence4: Some crab sipped some iced latte.
sentence4 = liftF (some crab) <| (return sipped |> liftF (some (iced latte)))


-- ===========
-- == Misc. ==
-- ===========

-- | Handle a sentence with effects, using a 'GetPutScopeHandler'.
handleSentence :: Handleable GetPutScopeHandler l '[] Bool ([Entity] -> Bool)
               => F l Bool -> F '[] ([Entity] -> Bool)
handleSentence = handle getPutScopeHandler

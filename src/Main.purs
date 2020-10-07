module Main where

import Prelude
import Rady

import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Show (genericShow)
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Console (log)

data Node = Node String (Array Node)
          | Text String

derive instance genericNode :: Generic Node _
instance showNode :: Show Node where show n = genericShow n

tagged :: ∀pat t. (Pattern pat Node t) => String -> pat -> Match Node t
tagged tagname pat = Match matchByTag (\xs -> Node tagname (generate pat xs))
  where matchByTag (Node tag xs) | (tagname == tag) = parse pat xs
        matchByTag _ = Nothing

anything :: ∀a. Star (Match a a)
anything = Star (Match pure (\a -> a))

text :: Match Node String
text = Match matchText Text
    where matchText (Text s) = Just s
          matchText _        = Nothing

minimal = tagged "head"
            (tagged "title" text
             `Interleave`
             anything)
          `Group`
          tagged "body"
            (anything)

parseMinimal :: Array Node → Maybe (Tuple (Tuple String (Array Node)) (Array Node))
parseMinimal = parse minimal

generateMinimal :: Tuple (Tuple String (Array Node)) (Array Node) → Array Node
generateMinimal = generate minimal

main :: Effect Unit
main = do
  log "🍝"

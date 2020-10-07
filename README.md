# purescript-rady
Encode/decode typed structures using a regular expression DSL.

Simple HTML/XML reader/generator in a few lines of code.

```
-- Abstract syntax of our Document (simplified)
data Node = Node String (Array Node)
          | Text String

-- A routine to match on tag.
tagged :: ∀pat t. (Pattern pat Node t) => String -> pat -> Match Node t
tagged tagname pat = Match matchByTag (\xs -> Node tagname (generate pat xs))
  where matchByTag (Node tag xs) | (tagname == tag) = parse pat xs
        matchByTag _ = Nothing

-- Matches any sequence in the structure.
anything :: ∀a. Star (Match a a)
anything = Star (Match pure (\a -> a))

-- Matches text nodes
text :: Match Node String
text = Match matchText Text
    where matchText (Text s) = Just s
          matchText _        = Nothing

minimal =
  tagged "head"
      (tagged "title" text
       `Interleave` anything)
  `Group`
  tagged "body" anything

```

```
> import Data.Tuple (Tuple(..))
> import Main
> import Rady
> generate minimal (Tuple (Tuple "Hello" []) [])
[(Node "head" [(Node "title" [(Text "Hello")])]),(Node "body" [])]

> parse minimal [(Node "head" [(Node "title" [(Text "Hello")])]),(Node "body" [])]
(Just (Tuple (Tuple "Hello" []) []))
```

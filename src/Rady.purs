module Rady where

import Data.Exists

import Control.Applicative (pure)
import Control.Apply ((<*>))
import Control.Bind (composeKleisli, (>>=))
import Control.Category (identity)
import Control.Semigroupoid ((<<<))
import Data.Array (concat, uncons, (:))
import Data.Array.NonEmpty (intersect)
import Data.Either (Either(..))
import Data.Eq ((==))
import Data.Foldable (foldl, intercalate)
import Data.Functor (map, (<$>))
import Data.Maybe (Maybe(..))
import Data.Semigroup ((<>))
import Data.Show (class Show, show)
import Data.Tuple (Tuple(..))
import Data.Unit (unit)
import Data.Void (Void, absurd)
import Prelude (Unit(..), bind)
import Unsafe.Coerce (unsafeCoerce)

matchAny :: ∀x. Match x x
matchAny = Match pure (\x -> x)

matchChar :: Char -> Match Char Char
matchChar char = Match (\a -> if a == char then Just a else Nothing) (\a -> a)

testpattern = (Group matchAny matchAny)

foo :: ∀ x. Tuple x x -> Array x
foo = generate testpattern

bar = parse testpattern

-- | Void       = Regex "[]"
data Reject         = Reject
-- | Empty      = Regex ""
data Empty          = Empty
-- | Match x t  = Regex "a"
data Match x t      = Match (x -> Maybe t) (t -> x)
-- | Tuple a b  = Regex "(ab)"
data Group a b      = Group a b
-- | Either a b = Regex "(a|b)"
data Alt a b        = Alt a b
-- (a+) = (aa*)
-- | Array a    = Regex "(a*)"
data Star a         = Star a
-- | Tuple a b  = Regex "(a&b)"
data Interleave a b = Interleave a b

--data Weak a         =

-- Generating the pattern is easy enough that it can be done directly.
-- To parse, we need to produce a pattern
-- that we can chop with the input.
class Pattern pattern symbol t | pattern -> symbol t where
    generate :: pattern -> t -> Array symbol
    pattern :: pattern -> P symbol t

parse :: ∀a x t. Pattern a x t => a -> Array x -> Maybe t
parse pat xs = accept (foldl deriv (pattern pat) xs)

-- In a sense these map to algebraic types.
-- 0 being Void, 1 being Unit,
-- describe the count of regular expressions they match to.
-- (specifically parse trees they can do)
instance patternReject :: Pattern Reject x Void where
    generate _ x = absurd x
    pattern _ = PReject

-- | When a matching symbol is chopped off the pattern,
-- | the pattern becomes "empty", but it needs to carry the result.
-- | Therefore instead of PEmpty, we got PAccept that gets the result.
instance patternEmpty :: Pattern Empty x Unit where
    generate _ _ = []
    pattern _ = PAccept unit

-- | Checks whether a function recognizes a symbol.
-- | Has an associated generator bundled along it.
-- |
-- | For example, this "match" function could match integer digits
-- | and transform them to Int, and back to string from there.
instance patternMatch :: Pattern (Match x t) x t where
    generate (Match f g) x = [g x]
    pattern (Match f g) = PMatch f

-- | Group represents sequencing, eg. "(ab)"
instance patternGroup :: (Pattern f x a, Pattern g x b)
                       => Pattern (Group f g) x (Tuple a b) where
    generate (Group f g) (Tuple x y) = generate f x <> generate g y
    pattern (Group f g) = (PGroup (mkExists2 (GroupF
                             {fst:pattern f, snd:pattern g, k:Tuple})))

instance patternAlt :: (Pattern f x a, Pattern g x b)
                       => Pattern (Alt f g) x (Either a b) where
    generate (Alt f g) (Left x) = generate f x
    generate (Alt f g) (Right y) = generate g y
    pattern (Alt f g) = PAlt (mkExists2 (AltF {fst:pattern f, snd:pattern g, k:(\a -> a)}))

instance patternStar :: (Pattern f x a)
                       => Pattern (Star f) x (Array a) where
    generate (Star f) xs = concat (map (generate f) xs)
    pattern (Star f) = (PStar (mkExists (StarF {p:pattern f, k:(:), e:[]})))

instance patternInterleave :: (Pattern f x a, Pattern g x b)
                       => Pattern (Interleave f g) x (Tuple a b) where
    generate (Interleave f g) (Tuple x y) = generate f x <> generate g y
    pattern (Interleave f g) = PInterleave (mkExists2 (GroupF {fst:pattern f, snd:pattern g, k:Tuple}))

data P x c = PReject
           | PAccept c
           | PMatch (x -> Maybe c)
           | PGroup (Exists2 (GroupF x c))
           | PAlt (Exists2 (AltF x c))
           | PStar (Exists (StarF x c))
           | PInterleave (Exists2 (GroupF x c))
           | PWith (Exists (ItemF x c))

data GroupF x c a b = GroupF { fst :: P x a
                             , snd :: P x b
                             , k :: a -> b -> c }

data AltF x c a b = AltF { fst :: P x a
                         , snd :: P x b
                         , k :: Either a b -> c }

data ItemF x c a = ItemF { p :: P x a
                         , k :: a -> c }

data StarF x c a = StarF { p :: P x a
                         , k :: a -> c -> c
                         , e :: c }

-- Quick note about ambiguity of a regular expression.

-- (a|a)   this expression has a match "a", which can produce (Left "a")
--                                                   but also (Right "a")
-- generate p (Left "a") >>> parse p = Left "a"
-- generate p (Right "a") >>> parse p = Left "a"
--
-- The structure is returned same,
-- only if the regular expression is unambiguous.
--
-- This may be a problem for some uses of the library.

-- Parsing with Derivatives:
--   You take the pattern
--   Take some symbol
--   Chop the symbol off the front of the pattern.

--   abb a --> bb
--   a   a --> ""

-- Uncons "abc" 'a' "bc"

deriv :: ∀x a. P x a -> x -> P x a
deriv PReject           a = PReject
deriv (PAccept _)       a = PReject
deriv (PMatch f)        a = case f a of
                            Nothing -> PReject
                            Just x -> PAccept x
deriv (PGroup box)      a = runExists2 (\(GroupF {fst, snd, k}) ->
                              -- The 'accept' catches
                              -- whether the first pattern
                              -- can accept an empty sequence.
                              case accept fst of
                                Just x -> alt vanish
                                          (group k (deriv fst a) snd)
                                          (group k (PAccept x) (deriv snd a))
                                Nothing -> (group k (deriv fst a) snd)) box
deriv (PAlt box)        a = runExists2 (\(AltF {fst, snd, k}) -> alt k (deriv fst a) (deriv snd a)) box
deriv (PStar box)       a = runExists (\(StarF {p, k, e}) -> 
                                group k (deriv p a) (PStar (mkExists (StarF {p, k, e})))) box
deriv (PInterleave box) a = runExists2 (\(GroupF {fst, snd, k}) ->
     alt vanish (interleave k (deriv fst a) snd) (interleave k fst (deriv snd a))
     ) box
deriv (PWith box)       a = runExists (\(ItemF {p, k}) -> case deriv p a of
                              PAccept x -> PAccept (k x)
                              PReject   -> PReject
                              p'        -> PWith (mkExists (ItemF {p:p', k:k}))) box

-- The `accept` produces a structure that was matched.

-- The PAlt in `accept` determines how ambiguous parses are treated. Now we catch the leftmost parse.
accept :: ∀ x a. P x a -> Maybe a
accept PReject           = Nothing
accept (PAccept x)       = Just x
accept (PMatch _)        = Nothing
accept (PGroup box)      = runExists2 (\(GroupF {fst, snd, k}) -> k <$> accept fst <*> accept snd) box
accept (PAlt box)        = runExists2 (\(AltF {fst, snd, k}) -> case accept fst of
    Just x -> pure (k (Left x))
    Nothing -> (k <<< Right) <$> accept snd) box
accept (PStar box)       = runExists (\(StarF {p, k, e}) -> Just e) box
accept (PInterleave box) = runExists2 (\(GroupF {fst, snd, k}) -> k <$> accept fst <*> accept snd) box
accept (PWith box)       = runExists (\(ItemF {p, k}) -> map k (accept p)) box

group :: ∀a b c x. (a -> b -> c) -> P x a -> P x b -> P x c
group k (PAccept x) g = PWith (mkExists (ItemF {p:g, k:k x}))
group k f (PAccept y) = PWith (mkExists (ItemF {p:f, k:(\x -> k x y)}))
group k PReject g = PReject
group k f PReject = PReject
group k f g = (PGroup (mkExists2 (GroupF {fst:f, snd:g, k:k})))

alt :: ∀a b c x. (Either a b -> c) -> P x a -> P x b -> P x c
alt k PReject g = PWith (mkExists (ItemF {p:g, k:(k <<< Right)}))
alt k f PReject = PWith (mkExists (ItemF {p:f, k:(k <<< Left)}))
alt k f g       = PAlt (mkExists2 (AltF {fst:f, snd:g, k:k}))

interleave :: ∀a b c x. (a -> b -> c) -> P x a -> P x b -> P x c
interleave k (PAccept x) g = PWith (mkExists (ItemF {p:g, k:k x}))
interleave k f (PAccept y) = PWith (mkExists (ItemF {p:f, k:(\x -> k x y)}))
interleave k PReject g = PReject
interleave k f PReject = PReject
interleave k f g = (PInterleave (mkExists2 (GroupF {fst:f, snd:g, k:k})))

foreign import data Exists2 :: (Type -> Type -> Type) -> Type

mkExists2 :: forall f a b. f a b -> Exists2 f
mkExists2 = unsafeCoerce

runExists2 :: forall f r. (forall a b. f a b -> r) -> Exists2 f -> r
runExists2 = unsafeCoerce

vanish :: ∀a. Either a a -> a
vanish (Left a)  = a
vanish (Right a) = a


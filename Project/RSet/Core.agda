------------------------------------------------------------------------
--
-- Reactive Sets
--
------------------------------------------------------------------------

module RSet.Core where

open import Data.Nat renaming (_∸_ to _-_)
open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Relation.Nullary
open import Relation.Binary.Core

open import Stream.Stream public
open import Stream.StreamUtils public

{-
RSet is a stream of types whose elements
are interpreted as temporal propositions at some index 
-}

RSet : ∀ {i} → Set₁
RSet {i} = Stream {i} Set

-- a vector representing a closed interval over RSet

_[_,_] : RSet → (s : ℕ) → (u : ℕ) → Vec Set (u - s)
A [ 0 , 0 ]         = []
A [ 0 , suc u ]     = take (suc u) A
A [ suc s , 0 ]     = []
A [ suc s , suc u ] = take ((suc u) - (suc s)) (drop s A)
getInterval = _[_,_]

-----------------------------------------------
-- liftings to RSet
-----------------------------------------------

¬ₛ_ : RSet → RSet
¬ₛ_ = lift1 ¬_

_×ₛ_ : RSet → RSet → RSet
_×ₛ_ = lift2 _×_

_⊎ₛ_ : RSet → RSet → RSet
_⊎ₛ_ = lift2 _⊎_

_→ₛ_ : RSet → RSet → RSet
_→ₛ_ = lift2 f where 
  f : Set → Set → Set
  f A B = A → B

_≡ₛ_ : ∀ {a} {A : Set a} → Stream A → Stream A → Stream (Set a)
_≡ₛ_ = lift2 _≡_

is : {A : Set} → (x : A) → Stream A → RSet
(is x) s = (x ▸⋯) ≡ₛ s



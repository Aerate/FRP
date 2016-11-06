------------------------------------------------------------------------
-- R⋯⟩ 
--
-- Reactive Sets
------------------------------------------------------------------------

module RSet.Core where

open import Size public
open import Stream.Stream public
open import Data.Nat
open import Data.Vec
open import Data.Fin
open import Data.Product
open import Data.Sum
open import Relation.Nullary
open import Relation.Binary.Core

-- RSet is a stream of types whose elements
-- are interpreted as (temporal) propositions at a given index 

RSet : ∀ {i} → Set₁
RSet {i} = Stream {i} Set


-- The elements of RSet may be inspected under temporal reading of now and later

record ⟦_⟧ (R : RSet) : Set where 
  coinductive
  constructor _►_   
  field
    now   : hd R 
    later : ⟦ tl R ⟧
open ⟦_⟧ public

-- ⟪ v ⟫ provides the structure for a vector of inhabitants in RSet

data ⟪_⟫ : {n : ℕ} (V : Vec Set n) → Set where
  []  : ⟪ [] ⟫ 
  _▹_ : {n : ℕ} → {v : Vec Set (suc n)} → head v → ⟪ tail v ⟫ → ⟪ v ⟫ 


-- liftings

¬ₛ_ : RSet → RSet
¬ₛ_ = mapₛ ¬_
ns_ = ¬ₛ_

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

_≡ₐ_ : {A : Set} → Stream A → Stream A → RSet
_≡ₐ_ = lift2 _≡_

_≢ₛ_ : {A : Set} → Stream A → Stream A → RSet
_≢ₛ_ = lift2 _≢_



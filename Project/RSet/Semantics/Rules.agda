module RSet.Semantics.Rules where

open import Data.Bool public
open import Function public
open import Data.Empty
open import Data.Unit
open import Relation.Binary.PropositionalEquality

open import RSet.Core

-- Iso
record _≈_ (A B : Set) : Set where
  constructor ≈ₛ 
  field
    f : A → B
    g : B → A
    invₗ : f ∘ g ≡ id
    invᵣ : g ∘ f ≡ id

embed : Bool → Set
embed true  = ⊤
embed false = ⊥

cont : Set → Set₁
cont B = (B → RSet) → RSet

_⊨_ : ∀ {B : Set} → (B → Stream Bool) → cont B → Set
(b ⊨ c) = hd (c ((lift1 embed) ∘ b))

-- scoped type variables in hs

atom : ∀ {B : Set} → B → cont B
atom b = λ g → (g b)

op : ∀ {B : Set} → (RSet → RSet) → cont B → cont B
op f c = f ∘ c

drop1 : ∀ {B : Set} → (B → Stream Bool) → (B → Stream Bool)
drop1 b = ((drop 1) ∘ b) 

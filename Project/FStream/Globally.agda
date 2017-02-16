module FStream.Globally where

open import FStream.Core

record ■A {c ℓ₁ ℓ₂} {A : Set ℓ₁} {C : Container c} (pred : A → Set ℓ₂) (cas : FStream C A) : Set (c ⊔ ℓ₂) where
  -- Zu jeder Zeit, bei jedem Seiteneffekt ist pred erfüllt
  coinductive
  field
    nowA   : APred {c} {ℓ₁} {ℓ₂} {C} {A} pred (map head (inF cas))
    laterA : APred {c} {ℓ₁ ⊔ c} {ℓ₂ ⊔ c} {C} {FStream C A} (■A pred) (map tail (inF cas))
open ■A public

record ■E {A : Set} {C : Container ℓ₀} (pred : A → Set) (cas : FStream C A) : Set where
  -- Jederzeit könnte ein Seiteneffekt auftreten, sodass pred erfüllt ist
  coinductive
  field
    nowE   : ◇ {ℓ₀} {C} {A} pred (map head (inF cas))
    laterE : ◇ {ℓ₀} {C} {FStream C A} (■E pred) (map tail (inF cas))
open ■E public


record ■A2 {C : Container ℓ₀} (cas : FStream C Set) : Set where
  coinductive
  field
    nowA2   : A (map head (inF cas))
    laterA2 : APred ■A2 (map tail (inF cas)) -- ∀ moegliche tails -> APred *
open ■A2 public

open import Relation.Binary
open import Size
open import Level
open import Stream.Stream
open import Data.Product

module Stream.Bisim.Bisim {ℓ} (S : Setoid ℓ ℓ) where

RT : ∀ {a b c d} → Set a → Set b → Set c → Set d → (ℓ₁ ℓ₂ : Level) → Set _
RT A₁ A₂ B₁ B₂ ℓ₁ ℓ₂ = REL A₁ A₂ ℓ₁ → REL B₁ B₂ ℓ₂

Rt : ∀ {a b} → Set a → Set b → (ℓ : Level) → Set _
Rt A B ℓ = RT A B A B ℓ ℓ

Monotone : ∀ {a b ℓ₁ ℓ₂} {A₁ A₂ : Set a} {B₁ B₂ : Set b} → RT A₁ A₂ B₁ B₂ ℓ₁ ℓ₂ → Set _
Monotone F = ∀ {R S} → R ⇒ S → F R ⇒ F S

open Setoid S renaming (Carrier to C; isEquivalence to S-equiv)

--infix 4 _~_

record _~_ {i : Size} (s t : Stream C) : Set ℓ where
  coinductive
  field
    hd≈ : hd s ≈ hd t
    tl~ : ∀ {j : Size< i} → _~_ {j} (tl s) (tl t)
open _~_ public

Φ : Rt (Stream C) (Stream C) ℓ
Φ R s t = (hd s ≈ hd t) × R (tl s) (tl t)

Φ-mono : Monotone Φ
Φ-mono R⇒S (h≈ , tR) = h≈ , (R⇒S tR)

--------------------


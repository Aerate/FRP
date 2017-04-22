module FStream.Core2 where

open import ContainerMonkeyPatched renaming (map to fmap)
open import Data.Product hiding (map)
open import Level
open import Size public


record FStream {i : Size} {ℓ₁ ℓ₂} (C : Container ℓ₁) (A : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  coinductive
  field
    inF : ⟦ C ⟧ (A × (∀ {j : Size< i} → FStream {j} C A))
open FStream


map : ∀ {i ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁} {A : Set ℓ₂} {B : Set ℓ₃} → (A → B) → FStream {i} C A → FStream {i} C B
inF (map {i} f as) = fmap < {!   !} , {!   !} > (inF {!   !})

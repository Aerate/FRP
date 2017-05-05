module FStream.Bisimulation where

open import Data.Product
open import Level renaming (suc to lsuc)
open import Function
open import Relation.Binary.PropositionalEquality
-- open import Relation.Binary.HeterogeneousEquality

open import FStream.Core
open import FStream.Modalities


record _∼_ {i} {ℓ₁ ℓ₂} {X : Set ℓ₁} {C : Container ℓ₂} (s₁ s₂ : FStream' {i} C X) : Set (ℓ₁ ⊔ ℓ₂) where
  coinductive
  field
    hd∼ : head s₁ ≡ head s₂
    sameShapes : ∀ {j : Size< i} → proj₁ (inF (tail s₁)) ≡ proj₁ (inF (tail s₂))
    tl∼ : ∀ {j : Size< i} → ∀ pos → (proj₂ (inF (tail s₁ {j})) pos ∼ proj₂ (inF (tail s₂ {j})) (subst (Position C) sameShapes pos))
open _∼_ public

record _⇒A_ {ℓ₁ ℓ₂} {C : Container ℓ₂} (s₁ s₂ : FStream' C (Set ℓ₁)) : Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
  coinductive
  field
    hd∼A : head s₁ → head s₂
    sameShapes : proj₁ (inF (tail s₁)) ≡ proj₁ (inF (tail s₂))
    tl∼A : ∀ pos → (proj₂ (inF (tail s₁)) pos ⇒A proj₂ (inF (tail s₂)) (subst (Position C) sameShapes pos))

-- TODO Generalise for arbitrary propositions


record _∼E_ {ℓ₁ ℓ₂} {X : Set ℓ₁} {C : Container ℓ₂} (s₁ s₂ : FStream' C X) : Set (ℓ₁ ⊔ ℓ₂) where
  coinductive
  field
    hd∼E : head s₁ ≡ head s₂
    sameShapesE : proj₁ (inF (tail s₁)) ≡ proj₁ (inF (tail s₂))
    tl∼E : ∃ λ pos → _∼E_ (proj₂ (inF (tail s₁)) pos) (proj₂ (inF (tail s₂)) (subst (Position C) sameShapesE pos))
open _∼E_ public

{-
_∼ₛ_ : ∀ {ℓ₁ ℓ₂} {X : Set ℓ₁} {C : Container ℓ₂} → (s₁ s₂ : FStream' C X) → FStream' C (Set (ℓ₁ ⊔ ℓ₂))
head (s₁ ∼ₛ s₂) = (head s₁ ≡ head s₂) × (proj₁ (inF (tail s₁))) ≡ (proj₁ (inF (tail s₂)))
--inF (tail (_∼ₛ_ {C = C} s₁ s₂)) = (proj₁ (inF (tail s₁))) , (λ pos → proj₂ (inF (tail s₁)) pos ∼ₛ proj₂ (inF (tail s₂)) (subst (Position C) (proj₂ (head {! s₁ ∼ₛ s₂  !})) pos) )
proj₁ (inF (tail (_∼ₛ_ {C = C} s₁ s₂))) = proj₁ (inF (tail s₁))
proj₂ (inF (tail (_∼ₛ_ {C = C} s₁ s₂))) pos = {!   !}
-- TODO Typ mit Wert vertauscht
-}






--

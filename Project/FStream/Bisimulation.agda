module FStream.Bisimulation where

open import Data.Product
open import Level renaming (suc to lsuc)
open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Binary
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

-- TODO Name is wrong, ' should go on the other version
-- TODO Maybe a mutual definition is more bearable (Same for FVec and a lot of proofs)
record _∼'_ {ℓ₁ ℓ₂} {X : Set ℓ₁} {C : Container ℓ₂} (s₁ s₂ : FStream C X) : Set (ℓ₁ ⊔ ℓ₂) where
  field
    sameInitShapes : proj₁ (inF s₁) ≡ proj₁ (inF s₂)
    bisim : ∀ pos → proj₂ (inF s₁) pos ∼ proj₂ (inF s₂) (subst (Position C) sameInitShapes pos)
open _∼'_ public

{-
BisimIsEquivalence : IsEquivalence _∼_
IsEquivalence.refl BisimIsEquivalence {x = x} = lemma x
  where
    lemma : ∀ {i} {ℓ₁ ℓ₂} {C : Container ℓ₁} → (s : FStream' {i} C (Set ℓ₂)) → s ∼ s
    hd∼ (lemma s) = refl
    sameShapes (lemma s) = refl
    tl∼ (lemma s) pos with inF (tail s)
    ...                      | shape , tails = lemma (tails pos)
IsEquivalence.sym BisimIsEquivalence {i = i} {j = j} = lemma i j
  where
    open Relation.Binary.PropositionalEquality._≡_
    lemma : ∀ {i} {ℓ₁ ℓ₂} {C : Container ℓ₁} → (s₁ s₂ : FStream' {i} C (Set ℓ₂)) → s₁ ∼ s₂ → s₂ ∼ s₁
    hd∼ (lemma s₁ s₂ bisim) = sym (hd∼ bisim)
    sameShapes (lemma s₁ s₂ bisim) = sym (sameShapes bisim)
    tl∼ (lemma {C = C} s₁ s₂ bisim) pos = {!   !}
    -- lemma (proj₂ (inF (tail s₁)) (subst (Position C) (sym (sameShapes bisim)) pos)) (proj₂ (inF (tail s₂)) pos) (tl∼ bisim ?)
IsEquivalence.trans BisimIsEquivalence {i = i} {j = j} {k = k} bisim₁ bisim₂  = lemma i j k bisim₁ bisim₂
  where
  lemma : ∀ {i} {ℓ₁ ℓ₂} {C : Container ℓ₁} → (s₁ s₂ s₃ : FStream' {i} C (Set ℓ₂)) → s₁ ∼ s₂ → s₂ ∼ s₃ → s₁ ∼ s₃
  hd∼ (lemma s₁ s₂ s₃ bisim₁ bisim₂) = trans (hd∼ bisim₁) (hd∼ bisim₂)
  sameShapes (lemma s₁ s₂ s₃ bisim₁ bisim₂) = trans (sameShapes bisim₁) (sameShapes bisim₂)
  tl∼ (lemma s₁ s₂ s₃ bisim₁ bisim₂) pos = {!   !}

-}



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

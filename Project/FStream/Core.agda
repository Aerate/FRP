module FStream.Core where

open import ContainerMonkeyPatched public
open import Relation.Binary.PropositionalEquality using (_≡_; refl) public
open import Data.Nat hiding (_⊔_) public
open import Data.Fin using (Fin; zero; suc) public
open import Data.Product hiding (map) public
open import Data.Unit using (tt; ⊤) public 
open import Level renaming (suc to ℓ⁺; zero to ℓ₀) public

mutual
  record FStream {ℓ₁ ℓ₂} (C : Container ℓ₁) (A : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
    inductive
    field
      inF : ⟦ C ⟧ (FStream' C A)
  record FStream' {ℓ₁ ℓ₂} (C : Container ℓ₁) (A : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
    coinductive
    field
      head : A
      tail : FStream C A
open FStream public
open FStream' public

repeat : {A : Set} → {C : Container  ℓ₀} → ⟦ C ⟧ A -> FStream C A
proj₁ (FStream.inF (repeat (proj₁ , proj₂))) = proj₁
FStream'.head (proj₂ (FStream.inF (repeat (proj₁ , proj₂))) x) = proj₂ x
FStream'.tail (proj₂ (FStream.inF (repeat ca)) x) = repeat ca

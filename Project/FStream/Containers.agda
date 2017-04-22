module FStream.Containers where

open import ContainerMonkeyPatched
open import Data.Nat hiding (_⊔_) public
open import Data.Fin hiding (_+_)
open import Level
open import Data.Product hiding (map) public
open import Data.Unit

ListC : Container Level.zero
Shape    ListC   = ℕ
Position ListC n = Fin n


StateC : ∀ {ℓ} → Set ℓ → Container ℓ
Shape (StateC S) = S → S
Position (StateC S) _ = S

ReaderC : Set → Container Level.zero
Shape (ReaderC R) = ⊤
Position (ReaderC R) _ = R

runReader : {R A : Set} → ⟦ ReaderC R ⟧ A → R → A
runReader (proj₁ , proj₂) r = proj₂ r

read : ∀ {R} → ⟦ ReaderC R ⟧ R
proj₁ read = tt
proj₂ read x = x

returnReader : {R A : Set} → A → ⟦ ReaderC R ⟧ A
returnReader a = tt , (λ _ → a)

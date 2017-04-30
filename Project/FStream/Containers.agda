module FStream.Containers where

open import ContainerMonkeyPatched
open import Data.Nat hiding (_⊔_) public
open import Data.Fin hiding (_+_)
open import Level renaming (zero to ℓ₀)
open import Data.Product hiding (map) public
open import Data.Unit
open import Data.Empty

ListC : Container ℓ₀
Shape    ListC   = ℕ
Position ListC n = Fin n

StateC : ∀ {ℓ} → Set ℓ → Container ℓ
Shape (StateC S) = S → S
Position (StateC S) _ = S

ReaderC : Set → Container ℓ₀
Shape (ReaderC R) = ⊤
Position (ReaderC R) _ = R

runReader : {R A : Set} → ⟦ ReaderC R ⟧ A → R → A
runReader (proj₁ , proj₂) r = proj₂ r

-- TODO Maybe rather follow Haskell convention and call it "ask"
read : ∀ {R} → ⟦ ReaderC R ⟧ R
proj₁ read = tt
proj₂ read x = x

returnReader : ∀ {ℓ} {A : Set ℓ} {R : Set} → A → ⟦ ReaderC R ⟧ A
returnReader a = tt , (λ _ → a)

IdC : Container ℓ₀
IdC = ⊤ ▷ (λ _ → ⊤)

Id : Set → Set
Id = ⟦ IdC ⟧

id : ∀ {X} → X → Id X
id x = tt , (λ _ → x)

kC : Set → Container ℓ₀
kC A = A ▷ (λ _ → ⊥)

K : Set → Set → Set
K A = ⟦ kC A ⟧

-- just a tryout
StreamC : Container ℓ₀
Shape StreamC = ⊤
Position StreamC _ = ℕ

CStream : Set → Set
CStream = ⟦ StreamC ⟧

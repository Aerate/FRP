module FStream.ModalitiesIdeas where

open import FStream.Core
open import FStream.Modalities
open import ContainerMonkeyPatched renaming (map to fmap)
open import Data.Product

open import Level
open import Function


GAₛ : ∀ {i} {A B : Set} (C : Container) → FStream {i} C A → FStream {i} C B
proj₁ (inF (GAₛ (Shape ▷ Position) x)) = {!!}
proj₂ (inF (GAₛ C x)) = {!!}

-- GAₛ' : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁} → FStream {i} C (Set ℓ₂) → FStream' {i} C (Set (ℓ₁ ⊔ ℓ₂))
-- head (GAₛ' cas) = GA cas
-- inF (tail (GAₛ' cas)) = fmap (GAₛ' ∘ (λ as → tail as)) (inF cas)

-- Aₛ : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁} → FStream {i} C (Set ℓ₂) → FStream' {i} C (Set (ℓ₁ ⊔ ℓ₂))
-- head (Aₛ {i} {ℓ₁} {ℓ₂} {C} cas) = A {ℓ₁} {ℓ₂} (fmap head (inF {i} cas))
-- inF (tail (Aₛ cas)) = fmap (Aₛ ∘ (λ as → tail as)) (inF cas)


-- Gₛ : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁} → FStream' {i} C (Set ℓ₂) → FStream {i} C (Set (ℓ₁ ⊔ ℓ₂))
-- inF (Gₛ cas) = fmap {!   !} {!   !}

-- -- Strategie für CTL*: Die temporalen Operatoren sammeln die F an, und die Effektoperatoren fressen sie alle auf
-- -- Brauchen wir freie Monaden dafür?
-- {-
-- Quasi so:
-- collect : FStream F A -> (Free F) (Stream A)
-- Dann A oder E anwenden
-- Wie dann in den F-Kontext zurückkehren?

-- Oder A & E sind nur Dekorationen per newtype die später ausgewertet werden
-- -}

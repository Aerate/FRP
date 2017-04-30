module FStream.ModalitiesIdeas where

open import FStream.Core
open import FStream.Modalities

open import Data.Product
open import Function
open import Level


-- GAₛ : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁} → FStream {i} C (Set ℓ₂) → FStream {i} C (Set (ℓ₁ ⊔ ℓ₂))
-- TODO Implement with fmap

{-
GAₛ' : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁} → FStream {i} C (Set ℓ₂) → FStream' {i} C (Set (ℓ₁ ⊔ ℓ₂))
head (GAₛ' cas) = GA cas
inF (tail (GAₛ' cas)) = fmap (GAₛ' ∘ (λ as → tail as)) (inF cas)
-}

-- TODO Das folgende kann ja gar nicht gehen, oder?
--GAₛ : ∀ {i} {A B : Set} (C : Container) → FStream {i} C A → FStream {i} C B
--proj₁ (inF (GAₛ (Shape ▷ Position) x)) = {!!}
--proj₂ (inF (GAₛ C x)) = {!!}

GAₛ' : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁} → FStream' {i} C (Set ℓ₂) → FStream' {i} C (Set (ℓ₁ ⊔ ℓ₂))
head (GAₛ' props) = GA' props
inF (tail (GAₛ' props)) = fmap GAₛ' (inF (tail props))

FAₛ' : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁} → FStream' {i} C (Set ℓ₂) → FStream' {i} C (Set (ℓ₁ ⊔ ℓ₂))
head (FAₛ' x) =  FA' x
inF (tail (FAₛ' x)) = fmap FAₛ' (inF (tail x))

FEₛ' : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁} → FStream' {i} C (Set ℓ₂) → FStream' {i} C (Set (ℓ₁ ⊔ ℓ₂))
head (FEₛ' x) =  FE' x
inF (tail (FEₛ' x)) = fmap FEₛ' (inF (tail x))

-- GAₛ' : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁} → FStream {i} C (Set ℓ₂) → FStream' {i} C (Set (ℓ₁ ⊔ ℓ₂))
-- head (GAₛ' cas) = GA cas
-- inF (tail (GAₛ' cas)) = fmap (GAₛ' ∘ (λ as → tail as)) (inF cas)


-- TODO The following is a crazy idea
{-
Gₛ : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁} → FStream' {i} C (Set ℓ₂) → FStream {i} C (Set (ℓ₁ ⊔ ℓ₂))
inF (Gₛ cas) = fmap {!   !} {!   !}


mutual
  FAₛ' : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁} → FStream {i} C (Set ℓ₂) → FStream' {i} C (Set (ℓ₁ ⊔ ℓ₂))
  head (FAₛ' props) = FA {!   !} -- props
  inF (tail (FAₛ' props)) = fmap FAₛ' (fmap (λ x → tail x) (inF props))
  FAₛ : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} → FStream  C (Set ℓ₂) → FStream C (Set (ℓ₁ ⊔ ℓ₂))
  FAₛ = {!   !}


FAₛ'' : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁} → FStream' {i} C (Set ℓ₂) → FStream' {i} C (Set (ℓ₁ ⊔ ℓ₂))
head (FAₛ'' {i} props) = FA' {! props  !} -- props
inF (tail (FAₛ'' props)) = fmap FAₛ'' (inF (tail props))

GAₛ'' : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁} → FStream' {i} C (Set ℓ₂) → FStream' {i} C (Set (ℓ₁ ⊔ ℓ₂))
GAₛ'' props = {!   !}
-}

--TODO Try GAₛ maybe?
--TODO Think about the semantics and implement it from there

-- Strategie für CTL*: Die temporalen Operatoren sammeln die F an, und die Effektoperatoren fressen sie alle auf
-- Brauchen wir freie Monaden dafür?
{-
Quasi so:
collect : FStream F A -> (Free F) (Stream A)
Dann A oder E anwenden
Wie dann in den F-Kontext zurückkehren?

Oder A & E sind nur Dekorationen per newtype die später ausgewertet werden
-}

Eₛ : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁} → FStream {i} C (Set ℓ₂) → FStream' {i} C (Set (ℓ₁ ⊔ ℓ₂))
head (Eₛ {i} {ℓ₁} {ℓ₂} {C} cas) = E {ℓ₁} {ℓ₂} (fmap head (inF {i} cas))
inF (tail (Eₛ cas)) = fmap (Eₛ ∘ (λ as → tail as)) (inF cas)

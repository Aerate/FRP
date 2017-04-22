module FStream.Modalities where

open import ContainerMonkeyPatched renaming (map to fmap)
open import FStream.Core public
open FStream public
open FStream' public

open import Data.Nat hiding (_⊔_)
open import Data.Fin hiding (_+_)
open import Data.Product hiding (map)
open import Data.Unit
open import Level
open import Function
open import Size public


{-

-- ■ und ◆ stehen für die temporalen Modalitäten, A und E stehen für die Seiteneffekt-Modalitäten

record ■A {c ℓ₁ ℓ₂} {A : Set ℓ₁} {C : Container c} (pred : A → Set ℓ₂) (cas : FStream C A) : Set (c ⊔ ℓ₂) where
  -- Zu jeder Zeit, bei jedem Seiteneffekt ist pred erfüllt
  coinductive
  field
    nowA : APred {c} {ℓ₁} {ℓ₂} {C} {A} pred (fmap head (inF cas))
    laterA : APred {c} {ℓ₁ ⊔ c} {ℓ₂ ⊔ c} {C} {FStream C A} (■A pred) (fmap tail (inF cas))
open ■A

data ◆E {A : Set} {C : Container Level.zero} (pred : A → Set) (cas : FStream C A) : Set where
  -- Irgendwann könnte ein Seiteneffekt auftreten, sodass pred erfüllt ist
  alreadyE : ◇ {Level.zero} {C} {A} pred (fmap head (inF cas)) → ◆E pred cas
  notYetE : ◇ {Level.zero} {C} {FStream C A} (◆E pred) (fmap tail (inF cas)) → ◆E pred cas
open ◆E




record ■E {A : Set} {C : Container Level.zero} (pred : A → Set) (cas : FStream C A) : Set where
  -- Jederzeit könnte ein Seiteneffekt auftreten, sodass pred erfüllt ist
  coinductive
  field
    nowE : ◇ {Level.zero} {C} {A} pred (fmap head (inF cas))
    laterE : ◇ {Level.zero} {C} {FStream C A} (■E pred) (fmap tail (inF cas))
open ■E


data ◆A {A : Set} {C : Container Level.zero} (pred : A → Set) (cas : FStream C A) : Set where
  -- Irgendwann ist ein Zeitpunkt erreicht, sodass unter jedem Seiteneffekt pred erfüllt wird
  alreadyA : □ {Level.zero} {C} {A} pred (fmap head (inF cas)) → ◆A pred cas
  notYetA : □ {Level.zero} {C} {FStream C A} (◆A pred) (fmap tail (inF cas)) → ◆A pred cas
open ◆A

-}

{-
record ■A2 {i} {C : Container Level.zero} (cas : FStream {i} C Set) : Set where
  coinductive
  field
    nowA2 : A (fmap head (inF cas))
    laterA2 : ∀ {j : Size< i} → APred ■A2 (fmap (tail {j}) (inF cas))
-}

record GA {i ℓ₁ ℓ₂} {C : Container ℓ₁} (cas : FStream {i} C (Set ℓ₂)) : Set (ℓ₁ ⊔ ℓ₂) where
  coinductive
  field
    nowA : A (fmap head (inF cas))
    laterA : {j : Size< i} → APred (GA {j}) (fmap (λ as → tail {i} as) (inF cas))

GAₛ : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁} → FStream {i} C (Set ℓ₂) → FStream {i} C (Set (ℓ₁ ⊔ ℓ₂))
inF (GAₛ cas) = {!   !}

GAₛ' : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁} → FStream {i} C (Set ℓ₂) → FStream' {i} C (Set (ℓ₁ ⊔ ℓ₂))
head (GAₛ' cas) = GA cas
inF (tail (GAₛ' cas)) = fmap (GAₛ' ∘ (λ as → tail as)) (inF cas)

Aₛ : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁} → FStream {i} C (Set ℓ₂) → FStream' {i} C (Set (ℓ₁ ⊔ ℓ₂))
head (Aₛ {i} {ℓ₁} {ℓ₂} {C} cas) = A {ℓ₁} {ℓ₂} (fmap head (inF {i} cas))
inF (tail (Aₛ cas)) = fmap (Aₛ ∘ (λ as → tail as)) (inF cas)

Gₛ : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁} → FStream' {i} C (Set ℓ₂) → FStream {i} C (Set (ℓ₁ ⊔ ℓ₂))
inF (Gₛ cas) = fmap {!   !} {!   !}
-- Strategie für CTL*: Die temporalen Operatoren sammeln die F an, und die Effektoperatoren fressen sie alle auf
-- Brauchen wir freie Monaden dafür?
{-
Quasi so:
collect : FStream F A -> (Free F) (Stream A)
Dann A oder E anwenden
Wie dann in den F-Kontext zurückkehren?

Oder A & E sind nur Dekorationen per newtype die später ausgewertet werden
-}


record GE {i ℓ₁ ℓ₂} {C : Container ℓ₁} (cas : FStream {i} C (Set ℓ₂)) : Set (ℓ₁ ⊔ ℓ₂) where
  coinductive
  field
    nowE : E (fmap head (inF cas))
    laterE : {j : Size< i} → EPred (GE {j}) (fmap {C = C} (λ as → tail {i} as) (inF cas))

data FA {i ℓ₁ ℓ₂} {C : Container ℓ₁} (cas : FStream {i} C (Set ℓ₂)) : Set (ℓ₁ ⊔ ℓ₂) where
  alreadyA : FA cas

{-
■A2 : {C : Container Level.zero} → (cas : FStream C Set) → Set
■A2 cas = ■A id cas
-}

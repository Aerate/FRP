module FStream.Modalities where

open import FStream.Core public

open import Data.Nat hiding (_⊔_)
open import Data.Fin hiding (_+_)
open import Data.Product hiding (map)
open import Data.Unit
open import Level
open import Size public


{-

-- ■ und ◆ stehen für die temporalen Modalitäten, A und E stehen für die Seiteneffekt-Modalitäten
-- Lieber G & F für die temporalen Modalitäten, ist klarer

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

record GA {ℓ₁ ℓ₂} {C : Container ℓ₁} (cas : FStream C (Set ℓ₂)) : Set (ℓ₁ ⊔ ℓ₂) where
  coinductive
  field
    nowA : A (fmap head (inF cas))
    laterA : APred GA (fmap (λ as → tail as) (inF cas))
open GA public

-- TODO Positivity is checked correctly in agda 2.6
{-# NO_POSITIVITY_CHECK #-}
record GA' {i : Size} {ℓ₁ ℓ₂} {C : Container ℓ₁} (props : FStream' {i} C (Set ℓ₂)) : Set (ℓ₁ ⊔ ℓ₂) where
  coinductive
  field
    nowA' : head props
    laterA' : {j : Size< i} → A (fmap GA' (inF (tail props)))
open GA' public

--TODO-Seb: GE'
record GE {ℓ₁ ℓ₂} {C : Container ℓ₁} (cas : FStream C (Set ℓ₂)) : Set (ℓ₁ ⊔ ℓ₂) where
  coinductive
  field
    nowE : E (fmap head (inF cas))
    laterE : EPred (GE) (fmap {C = C} (λ as → tail as) (inF cas))
open GE public

-- TODO From a CTL viewpoint, it makes much more sense that the modalities act on FStream',
-- since in the semantics, the first world is already given
--TODO-Seb: FA'
data FA {ℓ₁ ℓ₂} {C : Container ℓ₁} (cas : FStream C (Set ℓ₂)) : Set (ℓ₁ ⊔ ℓ₂) where
  alreadyA : A (fmap head (inF cas)) → FA cas
  notYetA : APred FA (fmap (λ x → tail x) (inF cas)) → FA cas
open FA

data FA' {ℓ₁ ℓ₂} {i : Size} {C : Container ℓ₁} (cas : FStream' {i} C (Set ℓ₂)) : Set (ℓ₁ ⊔ ℓ₂) where
  alreadyA : head cas → FA' cas
  notYetA :  {j : Size< i} →  A (fmap GA' (inF (tail cas))) → FA' cas
open FA'

--TODO-Seb: FE'
data FE {ℓ₁ ℓ₂} {C : Container ℓ₁} (cas : FStream C (Set ℓ₂)) : Set (ℓ₁ ⊔ ℓ₂) where
  alreadyE : E (fmap head (inF cas)) → FE cas
  notYetE : EPred FE (fmap (λ x → tail x) (inF cas)) → FE cas
open FE

{-
■A2 : {C : Container Level.zero} → (cas : FStream C Set) → Set
■A2 cas = ■A id cas
-}

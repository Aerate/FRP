module RSet.Globally where

open import RSet.Core
open import RSet.Next

record □ (R : RSet) : Set where
  coinductive
  constructor always_
  field
    □-now   : hd R
    □-later : □ (○ R)
open □ public

□ₛ : ∀ {i : Size} → RSet → RSet
hd (□ₛ x) = □ x
tl (□ₛ x) = □ₛ (tl x)

-- to be refined
never : ∀ {i : Size} → RSet → RSet
never = ¬ₛ_

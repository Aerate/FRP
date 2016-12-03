open import RSet.Core 

module RSet.Next where

data ○ₛ_ (R : RSet) : Set where
  next : (hd R) → ○ₛ R

○ : ∀ {i : Size} → RSet → RSet
○ A = tl A


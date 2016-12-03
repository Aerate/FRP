module RSet.Future where

open import RSet.Next
open import RSet.Core

data hd◇ (R : RSet) : Set where
  ◇-now   : (hd R) → hd◇ R
  ◇-later : (hd◇ (○ R)) → hd◇ R

◇ : ∀ {i : Size} → RSet → RSet
hd (◇ R) = hd◇ R
tl (◇ R) = ◇ (tl R)
eventually = ◇ 

module RSet.Future where

open import RSet.Next
open import RSet.Core

{-
For ◇ to be satisfiable over some RSet φ, 
φ has a witness now (and thus holds) or
φ needs to have a witness later (and thus holds)
-}

data hd◇ (φ : RSet) : Set where
  ◇-now   : (hd φ) → hd◇ φ
  ◇-later : (hd◇ (○ φ)) → hd◇ φ

-- constructing function for ◇
◇ : ∀ {i : Size} → RSet → RSet
hd (◇ R) = hd◇ R
tl (◇ R) = ◇ (tl R)
eventually = ◇ 

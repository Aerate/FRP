module Equality where

open import level

-- definitional equality
------------------------
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

id : (A : Set) → A → A
id A x = x

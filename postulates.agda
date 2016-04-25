module postulates where

{-- To my knowledge these postulates / axioms are already implemented
    in the language core; However, I'd like to have them explicitly
    for learning purposes and awareness of the underlying principles.
    This is work in progress.
    -
    In general I am not sure of the logical structure of "levels";
    The necessity seems to me to be of following order:
    Level -> atomic postulates about type-properties -> the logic
    one wants to build on this universe and its types.
--}

open import level

-- definitional equality
------------------------
data _≡_ {ℓ} {A : Set ℓ} (x : A) : A → Set ℓ where
  refl : x ≡ x

id : (A : Set) → A → A
id A x = x

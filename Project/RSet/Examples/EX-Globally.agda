module RSet.Examples.EX-Globally where

open import Data.Nat
open import Data.Product

open import RSet.Core
open import RSet.Globally
open import RSet.Properties.Reasoning

-- sugaring equality 

_isEqual_ : {A : Set} → A → A → Set 
_isEqual_ = _≡_

-- the trivial truth allows a recursive call for the '□-later' copattern
-- since it yields a constant stream of proof for 1 ≡ 1

check₁ : □ (1 isEqual 1 ▸⋯ )
□-now check₁ = refl
□-later check₁ = check₁

-- similar to the above, the following is now empty and later empty 

check₂ : □ (never (0 isEqual 1 ▸⋯))
□-now check₂ ()
□-later check₂ = check₂

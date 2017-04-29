module RSet.Examples.EX-Globally where

open import Data.Empty
open import Data.Nat
open import Data.Product hiding (map)
open import Relation.Nullary

open import RSet.Core
open import RSet.Globally
open import RSet.Globally.Proof
open import RSet.Properties.Reasoning

-- sugaring equality 

_isEqual_ : {A : Set} → A → A → Set 
_isEqual_ = _≡_

-- the trivial truth allows a recursive call for the '□-later' copattern
-- since it yields a constant stream of proof for 1 ≡ 1

check₁ : □ (1 isEqual 1 ▸⋯ )
□-now check₁ = refl
□-later check₁ = check₁

-- Since all the proofs are refl : 1 ≡ 1, we can just repeat it
check₁' : □ (1 isEqual 1 ▸⋯ )
check₁' = □repeat refl

-- similar to the above, the following is now empty and later empty

check₂ : □ (never (0 isEqual 1 ▸⋯))
□-now check₂ ()
□-later check₂ = check₂

-- TODO Need to find out whether this can be written with ⊥-elim
check₂' : □ (never (0 isEqual 1 ▸⋯))
check₂' = □map lemma
  where
    lemma : ¬ (0 ≡ 1)
    lemma ()


-- For RSets that aren't explicitly built with ▸⋯,
-- we first have to prove that they are equal to a construction with ▸⋯
check₃ : □ (map (_≡ 1) (1 ▸⋯))
check₃ = □map refl

check₄ : □ (map (_+ 1) (1 ▸⋯) ≡ₛ (2 ▸⋯))
check₄ = mapLemma


-- Again every statement can be proven with refl,
-- but the refls are of different types.
-- Therefore we need a vector of refls to cycle through.
cycleProof : □ ⟨ (1 ≡ 1) ▸ (2 ≡ 2) ⟩ ▸⋯
cycleProof = □cycle (refl □cons (refl □cons □nil))

cycleProof₂ : □ ((map (_+ 1) ⟨ 0 ▸ 1 ⟩ ▸⋯) ≡ₛ ⟨ 1 ▸ 2 ⟩ ▸⋯)
cycleProof₂ = vmapLemma

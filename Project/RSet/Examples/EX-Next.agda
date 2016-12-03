module RSet.Examples.EX-Next where

open import RSet.Core
open import RSet.Next
open import Data.Bool
open import RSet.Properties.Reasoning

-- get a stream of alternating booleans of form true ▸ false 

True-False : Stream Bool
True-False = ⟨ true ▸ (false ▸ []) ▸⋯ 

-- form a predicate over this stream, for example, is the stream true?

isTrue : Stream Bool → RSet
isTrue x = x ≡ₛ (true ▸⋯)

-- proposition 1: next true. Let's check:

check₁ : eval ○ (isTrue True-False)
validity check₁ = holds-not

-- proposition 2: next (next true)

check₂ : eval (○ (○ (isTrue True-False)))
validity check₂ = holds refl

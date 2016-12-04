open import RSet.Core 

open import Data.Nat

module RSet.Implication where

infix 1 _⇒_

_⇒_ : ∀ {i : Size} → RSet → RSet → RSet
ra ⇒ rb = ra →ₛ rb

[_⇒_] : RSet → RSet → ℕ → RSet
[ x ⇒ y ] n = ((x at n) → (y at n)) ▸⋯

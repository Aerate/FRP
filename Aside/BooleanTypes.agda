module BooleanTypes where

{-- Boolean Types and a few connectives. 
    Just definitions, no proofs here.
--}

open import level

-- Boolean Type
data 𝔹 : Set where
  tt : 𝔹
  ff : 𝔹


-- precedence rules 
-- The order is taken from https://en.wikipedia.org/wiki/Logical_connective

infix 8 ¬
infixr 6 _∧_
infixr 5 _∨_
infix 4 _⇒_

-- operations on Boolean Types

¬ : 𝔹 → 𝔹
¬ tt = ff
¬ ff = tt

_∧_ : 𝔹 → 𝔹 → 𝔹
tt ∧ b = b
ff ∧ b = ff

_∨_ : 𝔹 → 𝔹 → 𝔹
tt ∨ b = tt
ff ∨ b = b

_⇒_ : 𝔹 → 𝔹 → 𝔹
ff ⇒ _ = tt
tt ⇒ b = b

-- control flow 

if_then_else_ : ∀ {L} {A : Set L} → 𝔹 → A → A → A
if tt then A else B = A
if ff then A else B = B

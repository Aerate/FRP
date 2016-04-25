module Nat where

{-- Building a naive Type of Nats and a few operations with
    the basic knowledge from Haskell and λ-calculus.
    Used to experiment further with Types List and Vector.
    (Read: I didn't copy this from somewhere. Yay.)
--}

open import BooleanTypes

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

infixl 10 _*_
infixl 9 _+_ _-_
infixl 8 _<_ 

-- Induction and recursion over ℕ
-- !Q: Is the sig for natind actually the same as for natrec, where the props are just 'hidden' in Type C?
natrec : {C : Set} → C → (ℕ → C → C) → ℕ → C
natrec base step zero = base
natrec base step (suc n) = step n (natrec base step n)

natind : {P : ℕ → Set} → P zero → ((n : ℕ) → P n → P (suc n)) → (k : ℕ) → P k
natind base stepF zero = base
natind base stepF (suc n) = stepF n (natind base stepF n)

_+_ : ℕ → ℕ → ℕ
n + zero = n
n + (suc m) = suc (n + m)

_-_ : ℕ → ℕ → ℕ
zero - n = zero
n - zero = n
(suc m) - (suc n) = m - n

_*_ : ℕ → ℕ → ℕ
n * zero = zero
n * (suc m) = n + (n * m)

{-- It seems to me that this module is the wrong place
    for this kind of relation..
--}

_<_ : ℕ → ℕ → 𝔹
zero < zero = ff
zero < n = tt
n < zero = ff
(suc m) < (suc n) = (m < n) 

max : ℕ → ℕ → ℕ
max m n = if (m < n) then n else m





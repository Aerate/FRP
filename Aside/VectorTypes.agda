module VectorTypes where

open import Nat
open import postulates
open import BooleanTypes

data Vector (A : Set) : ℕ → Set where
  [] : Vector A 0
  _::_ : {n : ℕ} → A → Vector A n → Vector A (n + 1)

-- operations on Vectors
-----------------------

infixr 5 _::_

--only works with Vecs min 1 by sign, no base case needed
head : {A : Set} → {n : ℕ} → Vector A (suc n) → A
head (x :: _) = x

tail : {A : Set} → {n : ℕ} → Vector A (suc n) → Vector A n
tail (_ :: xs) = xs

[_]Vec : ∀ {A : Set} → A → Vector A 1
[ x ]Vec = x :: []

nats : (n : ℕ) → Vector ℕ (n + 1)
nats 0 = 0 :: []
nats (suc n) = (suc n) :: nats n

map : {A B : Set} → (f : A → B) → {n : ℕ} → Vector A n → Vector B n
map f [] = []
map f (x :: xs) = f x :: (map f xs)

-- they are the same type, but I do not know how to proove this
posnats : {n : ℕ} → tail (nats (suc n)) ≡ map suc (nats n)
posnats = {!!}

-- by autogive; y u no decomposition
length : {A : Set} → {n : ℕ} → Vector A n → ℕ
length = λ {A} {n} _ → n

-- compiles, but is broken (?); There is more to implicit and explicit
-- than I thought
length2 : (A : Set) → (n : ℕ) → Vector A n → ℕ
length2 = λ A n _ → n

-- but needs actual "look into" the Vector
length3 : {A : Set} → {n : ℕ} → Vector A n → ℕ
length3 [] = 0
length3 (x :: xs) = 1 + (length3 xs)

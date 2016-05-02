module VectorTypes where

open import Data.Nat 
open import Equality
open import Data.Bool

data Vector {a} (A : Set a) : ℕ → Set a where
  [] : Vector A 0
  _∷_ : ∀ {n} (x : A) (xs : Vector A n) → Vector A (suc n)

-- operations on Vectors
-----------------------

infixr 5 _∷_

head : ∀ {a n} {A : Set a} → Vector A (suc n) → A
head (x ∷ _) = x

tail : {A : Set} → {n : ℕ} → Vector A (suc n) → Vector A n
tail (_ ∷ xs) = xs

[_]Vec : ∀ {A : Set} → A → Vector A 1
[ x ]Vec = x ∷ []

map : {A B : Set} → (f : A → B) → {n : ℕ} → Vector A n → Vector B n
map f [] = []
map f (x ∷ xs) = f x ∷ (map f xs)

-- reverse
nats : (n : ℕ) → Vector ℕ (n + 1)
nats 0 = 0 ∷ []
nats (suc n) = 0 ∷ map suc (nats n)

posnats : {n : ℕ} → tail (nats (suc n)) ≡ map suc (nats n)
posnats = refl

length : {A : Set} → (n : ℕ) → Vector A n → ℕ
length n _ = n



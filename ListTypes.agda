module ListTypes where

open import postulates
open import BooleanTypes
open import Nat

infixr 6 _::_ _++_ 

data List {ℓ} (A : Set ℓ ) : Set ℓ where
  [] : List A
  _::_ : (x : A) (xs : List A) → List A

[_] : ∀ {ℓ} {A : Set ℓ} → A → List A
[ x ] = x :: []

length : ∀ {ℓ} {A : Set ℓ} →  List A → ℕ
length [] = zero
length (x :: xs) = suc (length xs)

_++_ : ∀ {ℓ} {A : Set ℓ} → List A → List A → List A
l1 ++ [] = l1
l1 ++ (x :: xs) = (x :: l1) ++ xs

l1 = (1 :: (2 :: (3 :: [])))
l2 = (4 :: (5 :: (6 :: [])))

con-corr : ∀ {ℓ} {A : Set ℓ} (l1 l2 : List A) → length (l1 ++ l2) ≡ (length l1) + (length l2)
con-corr [] l2 = refl
con-corr (x :: xs) l2 rewrite con-corr xs l2 = refl  

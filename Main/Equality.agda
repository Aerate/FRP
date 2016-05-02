module Equality where

open import Level

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

sym : ∀ {A} {a b : A} → a ≡ b → b ≡ a
sym refl = refl

trans : ∀ {A} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl refl = refl

cong : ∀ {A B} {m n : A} → (f : A → B) → m ≡ n → f m ≡ f n
cong f refl = refl

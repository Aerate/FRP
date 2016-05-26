module Streams where

open import Data.Nat
open import VectorTypes using (Vector; _∷_; [])
open import Equality

data Stream (A : Set) : Set where
  _◂_ : A → Stream A → Stream A   

map : {A B : Set} → (f : A → B) → Stream A → Stream B 
map f (x ◂ xs) = f x ◂ (map f xs)

head : {A : Set} → Stream A → A
head (x ◂ _) = x

tail : {A : Set} → Stream A → Stream A
tail (_ ◂ xs) = xs

take : {A : Set} → (n : ℕ) → Stream A → Vector A n
take zero _ = []
take (suc n) (x ◂ xs) = x ∷ (take n xs)

lemma1 : {A : Set} → (s : Stream A) → s ≡ (head s ◂ tail s)
lemma1 (x ◂ xs) = refl

lemma1-1 : {A : Set} → {x y : A} → {xs ys : Stream A} → (x ≡ y) → (xs ≡ ys) → (x ◂ xs) ≡ (y ◂ ys)
lemma1-1 refl refl = refl

streamEq : {A : Set} → {s1 s2 : Stream A} → (head s1 ≡ head s2) → (tail s1 ≡ tail s2) → (s1 ≡ s2)
streamEq {_} {(a ◂ as)} {(b ◂ bs)} h t = lemma1-1 h t

streamEq' : {A : Set} → {s1 s2 : Stream A} → (head s1 ≡ head s2) → (tail s1 ≡ tail s2) → (s1 ≡ s2)
streamEq' {_} {s1} {s2} h t = {!!}

{-# NON_TERMINATING #-}

strℕ : Stream ℕ
strℕ = 0 ◂ map suc strℕ 

{-# NON_TERMINATING #-}

strℕ₁ : Stream ℕ
strℕ₁ = 1 ◂ map suc strℕ₁

s1 = strℕ
s2 = strℕ₁

infixr 5 _~_

data _~_ {A} : (xs ys : Stream A) → Set where
  _◂_ : ∀ {x y xs ys} → (x ≡ y) → (xs ~ ys) → x ◂ xs ~ y ◂ ys

{-- ⁻\°-o/⁻
-The operators given in module Coinductive (∞,♯,♭), are they essential when handling coinductive types or are they just 'helpers'? (Haven't studied them yet)

-What about CoPatterns (Abel: http://www.lorentzcenter.nl/lc/web/2014/603/presentations/Abel.pdf), should I know about this?

-Is it possible to prove streamEq as stated above?
  -> why can't I pattern match on the equalities of the signature, at least on the first proposition 'headsProp' // how could I write a function that emits a bool or something like '(...) → ⊤ | ⊥'? 
  -> How should I use the lemma? I don't know how to deconstruct the matched propositions 'headsProp' and 'tailsProp'. 

-Is it necessary to understand bisimilarity / coinduction from a maths pov (would love to, but want to avoid falling in the maths rabbit hole)?

-Still unsure how agda exactly matches on equality patterns: when does it reduce to normalform, when will it not // is unable to?

-Is my take on proving streamEq naive as it is related to decidability? Why may I write a type that 'does' it (_~_), but a function (streamEq) eventually won't?
(Given that _~_ is correct, it compiles using 2.5.1)
-} 

module Streams where

open import Data.Nat
open import Data.Bool
--open import VectorTypes using (Vector; _∷_; [])
open import Data.Vec
--open import Equality
open import Relation.Binary.PropositionalEquality

data Stream (A : Set) : Set where
  _◂_ : A → Stream A → Stream A   

mapₛ : {A B : Set} → (f : A → B) → Stream A → Stream B 
mapₛ f (x ◂ xs) = f x ◂ (mapₛ f xs)

headₛ : {A : Set} → Stream A → A
headₛ (x ◂ _) = x

tailₛ : {A : Set} → Stream A → Stream A
tailₛ (_ ◂ xs) = xs

takeₛ : {A : Set} → (n : ℕ) → Stream A → Vec A n
takeₛ zero _ = []
takeₛ (suc n) (x ◂ xs) = x ∷ (takeₛ n xs)

lemma1 : {A : Set} → (s : Stream A) → s ≡ (headₛ s ◂ tailₛ s)
lemma1 (x ◂ xs) = refl

lemma1-1 : {A : Set} → {x y : A} → {xs ys : Stream A} → (x ≡ y) → (xs ≡ ys) → (x ◂ xs) ≡ (y ◂ ys)
lemma1-1 refl refl = refl

streamEq : {A : Set} → {s1 s2 : Stream A} → (headₛ s1 ≡ headₛ s2) → (tailₛ s1 ≡ tailₛ s2) → (s1 ≡ s2)
streamEq {_} {(a ◂ as)} {(b ◂ bs)} h t = lemma1-1 h t



streamEq' : {A : Set} → {s1 s2 : Stream A} → (headₛ s1 ≡ headₛ s2) → (tailₛ s1 ≡ tailₛ s2) → (s1 ≡ s2)
streamEq' {_} {(a ◂ as)} {(b ◂ bs)} h t = lemma1-1 h t

eq : {A B : Set} → (A ≡ B) →  Bool
eq refl = true 

t : ℕ ≡ ℕ
t = refl

{-# NON_TERMINATING #-}

s0 : Stream Bool
s0 = true ◂ s0

{-# NON_TERMINATING #-}

s1 : Stream Bool
s1 = false ◂ s1

--testEq : {A : Set} → {s1 s2 : Stream A} → streamEq → Bool
--testEq {_} {s1} {s2} x = true


{-# NON_TERMINATING #-}

strℕ : Stream ℕ
strℕ = 0 ◂ mapₛ suc strℕ 

{-# NON_TERMINATING #-}

strℕ₁ : Stream ℕ
strℕ₁ = 1 ◂ mapₛ suc strℕ₁

--s1 = strℕ
--s2 = strℕ₁

infixr 5 _~_

data _~_ {A} : (xs ys : Stream A) → Set where
  _◂_ : ∀ {x y xs ys} → (x ≡ y) → (xs ~ ys) → x ◂ xs ~ y ◂ ys



{-- ⁻\°-o/⁻
-The operators given in module Coinductive (∞,♯,♭), are they essential when handling coinductive types or are they just 'helpers'? (Haven't studied them yet)

-What about CoPatterns (Abel: http://www.lorentzcenter.nl/lc/web/2014/603/presentations/Abel.pdf), should I know about this?

-Is it possible to prove streamEq as stated above?
  -> why can't I pattern match on the equalities of the signature, at least on the first proposition 'headₛsProp' // how could I write a function that emits a bool or something like '(...) → ⊤ | ⊥'? 
  -> How should I use the lemma? I don't know how to deconstruct the matched propositions 'headₛysProp' and 'tailsProp'. 

-Is it necessary to understand bisimilarity / coinduction from a maths pov (would love to, but want to avoid falling in the maths rabbit hole)?

-Still unsure how agda exactly matches on equality patterns: when does it reduce to normalform, when will it not // is unable to?

-Is my take on proving streamEq naive as it is related to decidability? Why may I write a type that 'does' it (_~_), but a function (streamEq) eventually won't?
(Given that _~_ is correct, it compiles using 2.5.1)
-} 

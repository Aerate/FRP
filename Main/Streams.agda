module Streams where

open import Data.Nat
open import VectorTypes
open import Equality

data Stream (A : Set) : Set where
  _◂_ : A → Stream A → Stream A   

mapS : {A B : Set} → (f : A → B) → Stream A → Stream B 
mapS f (x ◂ xs) = f x ◂ (mapS f xs)

headS : {A : Set} → Stream A → A
headS (a ◂ as) = a

tailS : {A : Set} → Stream A → Stream A
tailS (a ◂ as) = as

take : {A : Set} → (n : ℕ) → Stream A → Vector A n
take zero _ = []
take (suc n) (a ◂ bs) = a ∷ (take n bs)

lem1 : {A : Set} → (s : Stream A) → s ≡ (headS s ◂ tailS s)
lem1 (a ◂ as) = refl


-- ⁻\°-o/⁻
{-# NON_TERMINATING #-}

strℕ : Stream ℕ
strℕ = 0 ◂ mapS suc strℕ 

--streamEq : {A : Set} → {s1 s2 : Stream A} → (headS s1 ≡ headS s2) → (tailS s1 ≡ tailS s2) → (s1 ≡ s2)
--streamEq {s1} {s2} eqH eqT = {refl\

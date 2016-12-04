module RSet.Properties.Reasoning where

open import Data.Bool
open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Relation.Binary.PropositionalEquality public
open import Relation.Binary.Core
open import Relation.Nullary.Decidable

open import RSet.Core
open import RSet

---------------------------------------------------
-- First steps towards naive evaluation
---------------------------------------------------

-- This kindof-Maybe acts as a 'wrapper' for 
-- matching on potentially empty sets

data ⟦_⟧? (R : RSet) : Set where
  holds     : (hd R) → ⟦ R ⟧?
  holds-not : ⟦ R ⟧?

-- evalutation 

record eval⟦_⟧ (R : RSet) : Set₁ where 
  coinductive
  field
    validity   : ⟦ R ⟧? 
-- add field(s) that print witness or lack of 
open eval⟦_⟧ public; eval_ = eval⟦_⟧

---------------------------------------------------
-- Decomposing RSet and embedding 
--
-- Get an element of some R ∈ RSet
-- and map them directly; 
-- 
-- To achieve this, the element must have a relation 
-- that is decidable
---------------------------------------------------

checkProp : {A : Set} → (r : Rel A ℓ₀) → (m n : A) → Decidable r → Set
checkProp r i j x = if ⌊ (x i j) ⌋ then ⊤ else ⊥

testCheck0 = checkProp (Data.Nat._≤_) 5 6 (Data.Nat._≤?_)
testCheck1 = checkProp (Data.Nat._≤_) 5 4 (Data.Nat._≤?_)
testCheck2 = checkProp (_≡_) 5 5 (Data.Nat._≟_)
testCheck3 = checkProp (_≡_) true false (Data.Bool._≟_)

{-
decompose : {A : Set} → (m : {i : Size} {a b : Level} {A : Set a} {B : Set b} → (A → B) → Stream A → Stream B) → (s : (section : ℕ) → Set) → (prim : Stream A) → Set 
decompose m s prim = {!!}
-}

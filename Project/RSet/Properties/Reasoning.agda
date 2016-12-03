module RSet.Properties.Reasoning where

open import Level
open import Data.Bool
open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Relation.Binary.PropositionalEquality public
open import Relation.Binary.Core
open import Relation.Nullary.Decidable
open import Relation.Nullary 

open import RSet.Core
open import RSet.Next
open import RSet.Future
open import RSet.Globally
open import RSet.Until

---------------------------------------------------
-- First steps towards naive evaluation
---------------------------------------------------

embed : Bool → Set
embed true  = ⊤
embed false = ⊥

-- kinda maybe
data ⟦_⟧? (R : RSet) : Set where
  holds     : (hd R) → ⟦ R ⟧?
  holds-not : ⟦ R ⟧?

-- add field(s) that gives witness
record eval⟦_⟧ (R : RSet) : Set₁ where 
  coinductive
  field
    validity   : ⟦ R ⟧? 
open eval⟦_⟧ public; eval_ = eval⟦_⟧

---------------------------------------------------
-- Decomposing RSet
--
-- Try to get back the parameters of some R ∈ RSet
---------------------------------------------------

checkProp : {A : Set} → (r : Rel A Level.zero) → (m n : A) → Decidable r → Set
checkProp r i j x = if ⌊ (x i j) ⌋ then ⊤ else ⊥

testCheck = checkProp (Data.Nat._≤_) 5 6 (Data.Nat._≤?_)
testCheck2 = checkProp (_≡_) 5 5 (Data.Nat._≟_)
testCheck3 = checkProp (_≡_) true false (Data.Bool._≟_)

{-
decompose : {A : Set} → (m : {i : Size} {a b : Level} {A : Set a} {B : Set b} → (A → B) → Stream A → Stream B) → (s : (section : ℕ) → Set) → (prim : Stream A) → Set 
decompose m s prim = {!!}
-}

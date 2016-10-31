module Stream.IDEAS.DecStream where

open import Level
open import Data.Bool
open import Stream.Stream
open import Stream.RSet
open import Relation.Nullary
open import Relation.Binary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality

data Setoidy : Set1 where
  setoidy : (A     : Set) 
                  → (_==_  : A -> A -> Set) → (refl  : (x : A) -> x == x) 
                  → (sym   : (x y : A) -> x == y -> y == x) 
                  → (trans : (x y z : A) -> x == y -> y == z -> x == z)
                  -> Setoidy

data DecS (P : Set) : Set where
  yes : ( p :   P) → DecS P
  no  : (¬p : ¬ P) → DecS P

infix 4 _≡?_

RRel : ∀ {a} → Set a → (ℓ : Level) → Set (a ⊔ suc ℓ)
RRel A ℓ = REL A A ℓ

_≡?_ : Decidable {A = RSet} _≡_
x ≡? y = {!!}

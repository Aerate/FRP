module Stream.IDEAS.Pointwise where

open import Relation.Binary
--open import Data.Vec
open import Stream.Stream
open import Size

infixr 5 _∷ₚ_

data Pointwise {ℓ} {A B : Set ℓ} (_∼_ : REL A B ℓ) : (xs : Stream A) (ys : Stream B) → Set ℓ where
  _∷ₚ_ : ∀ {x y} {xs : Stream A} {ys : Stream B} (x∼y : x ∼ y) (xs∼ys : Pointwise _∼_ xs ys) → Pointwise _∼_ (x ∷ xs) (y ∷ ys)


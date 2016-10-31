module Stream.Tries.new where

open import Stream.Semantics
open import Function
open import Stream.Stream
open import Data.Empty
open import Data.Product
open import Data.Unit
open import Data.Bool
open import Data.Vec hiding (_⋎_) renaming (_∷_ to _▸_)
open import Relation.Binary.PropositionalEquality
open import Category.Monad.Identity

data EinSet : Set where
  eins : EinSet

helperBool : {B : Set} → B → Stream Bool
helperBool x = ⟨ (true ▸ false ▸ []) ▸⋯

s : Set → Stream Set
hd (s x) = x
tl (s x) = s x

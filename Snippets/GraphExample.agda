open import Data.List 
open import Data.Nat
open import Relation.Binary.Core
open import Data.Maybe

record Context (Node : Set) : Set where
  constructor c
  field
    label : Node
    succs : List Node

data Graph (Node : Set) : Set where
  ∅ : Graph Node
  _&_ : Context Node → Graph Node → Graph Node

dreieck : Graph ℕ
dreieck = c 1 (2 ∷ 1 ∷ []) & ∅

maybeHead : {a : Set} → List a → Maybe a
maybeHead [] = nothing
maybeHead (a ∷ _) = just a

connections : {Node : Set} → Graph Node → Node → Maybe Node
connections ∅ _ = nothing
connections (c node1 list & g) node2 = maybeHead list


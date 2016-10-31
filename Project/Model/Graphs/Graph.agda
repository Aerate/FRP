module Model.Graphs.Graph where

open import Data.Fin
open import Stream.Stream
open import RSet.RSet
open import Data.Empty
open import Data.Unit
open import Data.Vec hiding (_⋎_) renaming (_∷_ to _▸_)

record Graph (Node : Set) : Set₁ where
  constructor g
  field
    edges : Node → Node → Set

record Path (Node : Set) (g : Graph Node) : Set where
  constructor p 
  field 
    nodes : Stream Node
    cont  : ⟦ lift2 (Graph.edges g) nodes (tl nodes) ⟧

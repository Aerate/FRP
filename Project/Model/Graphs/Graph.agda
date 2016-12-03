------------------------------------------------------------------------
-- R⋯⟩ 
-- 
-- Outline of the graph data structure 
------------------------------------------------------------------------

module Model.Graphs.Graph where

open import Data.Fin
open import Stream.Stream
open import RSet.Core
open import Data.Empty
open import Data.Unit

record Graph (Node : Set) : Set₁ where
  constructor g
  field
    edges : Node → Node → Set

-- A (potentially infinite) path in a graph
-- is a sequence of nodes s.t. its stream representation
-- denotes the start as (hd Stream) and the subsequent path as (tl Stream)

record Path (Node : Set) (g : Graph Node) : Set where
  constructor p 
  field 
    nodes : Stream Node
    cont  : ⟦ lift2 (Graph.edges g) nodes (tl nodes) ⟧

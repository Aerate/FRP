module  Model.Graphs.EX-Graphs where

open import Model.Graphs.Graph
open import Data.Fin
open import Stream.Stream 
open import RSet.Core
open import Data.Empty
open import Data.Unit

-- Example
-- 0 <---------+
-- |           |
-- |           |
-- |           |
-- +---------> 1

g1 : Graph (Fin 2)
Graph.edges g1 zero zero = ⊥
Graph.edges g1 zero (suc zero) = ⊤
Graph.edges g1 zero (suc (suc ()))
Graph.edges g1 (suc zero) zero = ⊤
Graph.edges g1 (suc (suc ())) zero
Graph.edges g1 (suc zero) (suc zero) = ⊥
Graph.edges g1 (suc (suc ())) (suc zero)
Graph.edges g1 (suc x) (suc (suc ()))

-- 0 -> 1
p1 : Path (Fin 2) g1
Path.nodes p1 = ⟨ zero ▸ (suc zero) ⟩ ▸⋯
now (Path.cont p1) = tt
now (later (Path.cont p1)) = tt
later (later (Path.cont p1)) = Path.cont p1

-- 1 -> 0
p2 : Path (Fin 2) g1
Path.nodes p2 = ⟨ (suc zero) ▸ zero ⟩ ▸⋯
now (Path.cont p2) = tt
now (later (Path.cont p2)) = tt
later (later (Path.cont p2)) = Path.cont p2

-- p1 and p2 never cross ("no collision")
noCrossing : ⟦ ¬ₛ (Path.nodes p1 ≡ₛ Path.nodes p2) ⟧
now noCrossing ()
now (later noCrossing) ()
later (later noCrossing) = noCrossing

------------------------------------------------------------------------
--
-- Properties of stream equivalence and bisimulation principle
--
------------------------------------------------------------------------

module Stream.StreamEq where

open import Stream.Stream
open import RSet.Core
open import RSet.Globally

open import Data.Product
open import Relation.Binary.PropositionalEquality

-- two Streams are equal if they are pointwise equal ∀ {i}
record _~ₛ_  {a : Level} {A : Set a} (s1 s2 : Stream A) : Set a  where
  coinductive
  field
    hd~ : hd s1 ≡ hd s2
    tl~ : tl s1 ~ₛ tl s2
open _~ₛ_ public

-- TODO Implement Relation.Binary.EqReasoning for this

-- Bisimulations*
-- idea: two coalgebras X → F(X) and Y → F(Y) s.t. x ∈ X & y ∈ Y are bisimilar ∀ {i : Index (Size)} (i.e. ext-equiv)
record Bisim  {i : Size} {a : Level} {A X Y : Set a} (c : X → A × X) (d : Y → A × Y) (x : X) (y : Y) : Set a where
  coinductive
  field
    hdB : proj₁ (c x) ≡ proj₁ (d y)
    tlB : ∀ {j : Size< i} → Bisim {j} c d (proj₂ (c x)) (proj₂ (d y))
open Bisim public

-- Apply*
∃-Bisim : ∀ {a} {A X Y : Set a} (c : X → A × X) (d : Y → A × Y) (x : X) (y : Y) → Bisim c d x y → (corec c x) ~ₛ (corec d y)
hd~ (∃-Bisim c d x y p) = hdB p
tl~ (∃-Bisim c d x y p) = ∃-Bisim c d x' y' (tlB p) where
      x' = proj₂ (c x)
      y' = proj₂ (d y)

{-
data _≡ₛ_ {a : Level} {A : Set a} (s1 s2 : Stream A) : Set a  where
  s≡s : s1 ~ₛ s2 → s1 ≡ₛ s2
-}

-- If one can bisimulate two streams, then one can show equality for all time
-- TODO Ponder whether to make A (and □) universe-polymorphic
~ₛ→≡ₛ : ∀ {A : Set} {s1 s2 : Stream A} → s1 ~ₛ s2 → □ (s1 ≡ₛ s2)
□-now (~ₛ→≡ₛ x) = hd~ x
□-later (~ₛ→≡ₛ x) = ~ₛ→≡ₛ (tl~ x)

-- code (*) adapted from https://github.com/hbasold

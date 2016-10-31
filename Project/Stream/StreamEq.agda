module Stream.StreamEq where

open import Stream.Stream
open import Size
open import Level
open import Data.Product
open import Relation.Binary.PropositionalEquality

-- two Streams are equal if they are pointwise equal ∀ {i}
record _~ₛ_  {a : Level} {A : Set a} (s1 s2 : Stream A) : Set a  where
  coinductive
  field
    hd~ : hd s1 ≡ hd s2
    tl~ : tl s1 ~ₛ tl s2
open _~ₛ_ public

-- Bisimulations* 
-- idea: two coalgebras X → F(X) and Y → F(Y) s.t. x ∈ X & y ∈ Y are bisimilar ∀ {i} (i.e. ext-equiv)
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
* after https://github.com/hbasold
see also:
cs.ioc.ee/ewscs/2011/jacobs/jacobs-slides.pdf
http://homepages.cwi.nl/~janr/papers/files-of-papers/2011_Jacobs_Rutten_new.pdf
-}

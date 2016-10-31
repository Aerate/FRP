module Stream.StreamEq where

open import Stream.Stream
open import Size
open import Level
open import Data.Product
open import Relation.Binary.PropositionalEquality


-- two Streams are equal if they are pointwise equal ∀ {i}
record _~ₛ_ {i : Size} {a : Level} {A : Set a} (s1 s2 : Stream  {i} A) : Set (suc a)  where
  coinductive
  field
    hd~ : hd s1 ≡ hd s2
    tl~ : ∀ {j : Size< i} → tl s1 ~ₛ tl s2 {j}
open _~ₛ_ public

s≡s : {a : Level} {A : Set a} → (s : Stream A) → s ≡ s 
s≡s s = refl

-- cong fuer sizes => funktioniert oder funktioniert nicht?
--s~ₛs : {i : Size} → {a : Level} {A : Set a} → (s1 s2 : Stream {i} A) → s1 ≡ s2 → s1 ~ₛ s2
--hd~ (s~ₛs s1 s2 x) = cong hd x 
--tl~ (s~ₛs {i} s1 s2 x) {j} = s~ₛs {j} (tl s1 {j}) (tl s2 {j}) {!!}

-- Bisimulations* 
-- idea: two coalgebras X → F(X) and Y → F(Y) s.t. x ∈ X & y ∈ Y are bisimilar ∀ {i} (i.e. ext-equiv)
record Bisim  {i : Size} {a : Level} {A X Y : Set a} (c : X → A × X) (d : Y → A × Y) (x : X) (y : Y) : Set (suc a) where
  coinductive
  field
    hdB : proj₁ (c x) ≡ proj₁ (d y)
    tlB : ∀ {j : Size< i} → Bisim {j} c d (proj₂ (c x)) (proj₂ (d y))
open Bisim public

-- -- Apply principle*
-- -- we have 'c' and 'd' and initials 'x' and 'y', show there is a Bisim at {i=0} and apply at {i+n} 
∃-Bisim : ∀ {a} {A X Y : Set a} (c : X → A × X) (d : Y → A × Y) (x : X) (y : Y) → Bisim c d x y → (corec c x) ~ₛ (corec d y)
hd~ (∃-Bisim c d x y p) = hdB p
tl~ (∃-Bisim c d x y p) = ∃-Bisim c d x' y' (tlB p) where
      x' = proj₂ (c x)
      y' = proj₂ (d y)
      --j  = Size< i

-- -- Todo (where we want to go)
-- postulate equals : ∀ {a} {A X Y : Set a} {s1 s2 : Stream A} (c : X → A × X) (d : Y → A × Y) (x : X) (y : Y) → (corec c x) ~ₛ (corec d y) → s1 ≡ s2


-- {-
-- * after https://github.com/hbasold
-- see also:
-- cs.ioc.ee/ewscs/2011/jacobs/jacobs-slides.pdf
-- http://homepages.cwi.nl/~janr/papers/files-of-papers/2011_Jacobs_Rutten_new.pdf
-- -}

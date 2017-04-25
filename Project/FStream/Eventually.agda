module FStream.Eventually where

open import FStream.Core

data ◆E {A : Set} {C : Container ℓ₀} (pred : A → Set) (cas : FStream C A) : Set where
  -- Irgendwann könnte ein Seiteneffekt auftreten, sodass pred erfüllt ist
  alreadyE : ◇ {ℓ₀} {C} {A} pred (map head (inF cas)) → ◆E pred cas
  notYetE  : ◇ {ℓ₀} {C} {FStream C A} (◆E pred) (map tail (inF cas)) → ◆E pred cas
open ◆E public

data ◆A {A : Set} {C : Container ℓ₀} (pred : A → Set) (cas : FStream C A) : Set where
  -- Irgendwann ist ein Zeitpunkt erreicht, sodass unter jedem Seiteneffekt pred erfüllt wird
  alreadyA : □ {ℓ₀} {C} {A} pred (map head (inF cas)) → ◆A pred cas
  notYetA  : □ {ℓ₀} {C} {FStream C A} (◆A pred) (map tail (inF cas)) → ◆A pred cas
open ◆A public

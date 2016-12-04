open import RSet.Core 
open import RSet.Next
open import RSet.Until

module RSet.Release where

{-
ψ has to hold until either φ holds and releases the constraint on ψ,
or ψ has to hold potentially infinitely.
-}

data _R_ (φ ψ : RSet) : Set where
  rel   : hd φ → hd ψ → φ R ψ 
  _noR_ : hd ψ → ○ φ R ψ → φ R ψ

_Release_ : RSet → RSet → RSet
hd (φ Release ψ) = φ R ψ
tl (φ Release ψ) = (○ φ) Release (○ ψ)

{-
An alternative definition in terms of Until
-}

_Releaseᵤ_ : RSet → RSet → RSet
φ Releaseᵤ ψ = ¬ₛ ((¬ₛ φ) Until (¬ₛ ψ))

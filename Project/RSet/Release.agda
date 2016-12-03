open import RSet.Core 
open import RSet.Next

module RSet.Release where


{-
φ either holds and releases the constraint ψ,
or ψ has to hold until φ
-}

data _R_ (φ ψ : RSet) : Set where
  rel   : hd φ → φ R ψ 
  _noR_ : hd ψ → ○ φ R ψ → φ R ψ

_Release_ : RSet → RSet → RSet
hd (φ Release ψ) = φ R ψ
tl (φ Release ψ) = (○ φ) Release (○ ψ)

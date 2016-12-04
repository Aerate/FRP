open import RSet.Core 
open import RSet.Next

module RSet.Until where

{-
ψ has to hold at least until φ holds
-}

data _U_ (φ ψ : RSet) : Set where
  finally : hd φ → φ U ψ
  _until_ : hd ψ → (○ ψ) U (○ ψ) → φ U ψ

_Until_ : RSet → RSet → RSet
hd (R Until S) = R U S
tl (R Until S) = (○ R) Until (○ S)

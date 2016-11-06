open import RSet.Core 
open import RSet.Next

module RSet.Until where

data _hdU_ (R S : RSet) : Set where
  finally : hd S → R hdU S
  _until_ : hd R → (○ R) hdU (○ S) → R hdU S

_U_ : RSet → RSet → RSet
hd (R U S) = R hdU S
tl (R U S) = (○ R) U (○ S)

module LTL.Main where

open import Size
open import Stream.Stream
open import Data.Nat
open import LTL.Data.Ampel
open import Data.Bool
open import Prelude
open import Data.Vec

data Even : ℕ → Set where
  evenZero : Even 0
  evenSuc : {n : ℕ} → Even n → Even (suc (suc n))

isEven : ℕ → Bool
isEven n with (n mod 2)
... | 0 = true
... | _ = false

timeSwitch : ℕ → Ampel
timeSwitch n with isEven n
... | true  = gruen
... | false = rot

crossing : (s1 s2 : Stream Ampel) → Stream (Ampel × Ampel)
hd (crossing s1 s2) = (hd s1) , (hd s2) 
tl (crossing s1 s2) = crossing (tl s1) (tl s2)

-- Eine Kreuzung
-- NS = Nord-Süd, OW = Ost-West

AmpelNS : Stream Ampel
AmpelNS = toStr timeSwitch

AmpelOW : Stream Ampel
AmpelOW = mapₛ switch AmpelNS

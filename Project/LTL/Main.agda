module LTL.Main where

open import Size
open import Stream.Stream
open import Stream.StreamEq
open import Data.Nat hiding (_+_)
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

--AmpelNS' : Stream Ampel
--AmpelNS' = corec (λ x → switch x , gruen) rot

constrot : Stream Ampel
constrot = repeat rot

rot1 : constrot ≡ₛ constrot
hd≡ rot1 = refl
tl≡ rot1 = rot1

eq1 : AmpelNS ≡ AmpelNS
eq1 = refl

eq2 : AmpelNS ≡ₛ AmpelNS
eq2 = s≡ₛs AmpelNS AmpelNS refl

safe : (s1 s2 : Stream Ampel) → Stream (Ampel × Ampel)
hd (safe s1 s2) = (hd s1) , (notₐ (hd s2))
tl (safe s1 s2) = safe (tl s1) (tl s2)

--data Safe (T : Stream (Ampel × Ampel)) : Set where
--   safe' : ∀ {s1 s2 : Stream Ampel} → Safe T

-- nur rot-gruen! (beachte rot-rot..)
record Safe (s1 s2 : Stream Ampel) : Set where
  coinductive
  field 
    now   : (hd s1) ≡ (notₐ (hd s2))
    later : Safe (tl s1) (tl s2) 

lem1 : (a1 : Ampel) → a1 ≡ (notₐ (switch a1))
lem1 gruen = refl
lem1 rot = refl

safeAmpel' : (s : Stream Ampel) → Safe s (m switch s)
Safe.now (safeAmpel' s) = lem1 (hd s)
Safe.later (safeAmpel' s) = safeAmpel' (tl s)

safeAmpel : Safe AmpelNS AmpelOW
safeAmpel = safeAmpel' AmpelNS


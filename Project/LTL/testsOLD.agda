module LTL.testsOLD where

open import FRP.LTL.RSet
open import Stream.Stream
open import Stream.StreamEq
open import Data.Vec
open import Data.Nat hiding (_+_) renaming (_≟_ to _≟n_)
open import LTL.Data.Ampel
--open import Data.Product
open import FRP.LTL.Time hiding (_,_)
open import Prelude
open import Agda.Builtin.Nat public using (_==_)

open import LTL.Main

--instance postulate myTime : Time

timeStream : Stream Time
hd timeStream = 0
tl timeStream = toStr suc

timeSwitch' : Time → Ampel
timeSwitch' n with isEven n
... | true  = gruen
... | false = rot
ts = timeSwitch'

atTime : ∀ {A : Set} → Stream A → Time → A
atTime xs t = xs at t

a1 : Time → ⟦ ⟨ Ampel ⟩ ⟧ 
a1 t = ts t

toℕ : Time → ℕ
toℕ t = t

Signal : Set → Set
Signal(A) = Time → A

μ : ∀ {A : Set} → ⟦ ⟨ ⟦ ⟨ A ⟩ ⟧ ⟩ ⟧ → ⟦ ⟨ A ⟩ ⟧
μ(σ) {t} = σ {t} {t}

E : RSet → RSet
E(A)(t) = Maybe(A(t))

--postulate 
--  mouseButtonState : Set
--  MouseEvent : Set
--  mouseButton : Signal(mouseButtonState)
--  mouseClick : Signal(Maybe(MouseEvent))

data mouseButtonState : Set where
  up   : mouseButtonState
  down : mouseButtonState

data MouseEvent : Set where
  clicked : MouseEvent

mbs : RSet
mbs = ⟨ mouseButtonState ⟩

mouseButton : ⟦ ⟨ mouseButtonState ⟩ ⟧
mouseButton {zero} = up
mouseButton {suc t} = down

mouseClick : ⟦ E ⟨ MouseEvent ⟩ ⟧
mouseClick {5} = just clicked
mouseClick {_} = nothing

tester : (t1 : Time) → ⟨ mouseButtonState ⟩ t1
tester zero = up
tester (suc t1) = down

aux : (t : Time) → ⟨ mouseButtonState ⟩ t → Bool
aux t up = true
aux t down = false

--clickMon : ⟦ ⟨ mouseButtonState ⟩ ⟧ → ⟦ E ⟨ MouseEvent ⟩ ⟧
--clickMon s{t} = if aux t s then just clicked else nothing


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

-- nur rot-gruen! (beachte rot-rot..)
record Safe (s1 s2 : Stream Ampel) : Set where
  coinductive
  field 
    now   : (hd s1) ≡ (notₐ (hd s2))
    later : Safe (tl s1) (tl s2) 

--safeAmpel : Safe AmpelNS AmpelOW
--Safe.now safeAmpel = refl
--Safe.later safeAmpel = {!!}


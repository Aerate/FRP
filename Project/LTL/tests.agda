module LTL.tests where

open import FRP.LTL.RSet
open import Stream.Stream
open import Data.Vec
open import Data.Nat hiding (_+_) renaming (_≟_ to _≟n_)
open import LTL.Data.Ampel
open import Data.Product
open import FRP.LTL.Time
open import Prelude
open import Agda.Builtin.Nat public using (_==_)

open import LTL.Main

--instance postulate myTime : Time

timeStream : Stream Time
hd timeStream = 0
tl timeStream = toStr suc

t0 t1 t2 t5 : Time
t0 = 0
t1 = 1
t2 = 2
t5 = 5

RAmpel : RSet
RAmpel = ⟨ Ampel ⟩

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

clickMon : ⟦ ⟨ mouseButtonState ⟩ ⟧ → ⟦ E ⟨ MouseEvent ⟩ ⟧
clickMon s{t} = if aux t s then just clicked else nothing


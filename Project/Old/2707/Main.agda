module Main where

--open import FRP.LTL.RSet
--open import FRP.LTL.ISet
open import FRP.LTL.Util
--open import FRP.LTL.Time
open import Data.Nat renaming (_+_ to _+ₙ_)
open import Data.Product using ( ∃ ; _×_ ; _,_ )
open import FRP.LTL.RSet.Stateless

Time : Set
Time = ℕ

RSet : Set₁
RSet = Time → Set

⟨_⟩ : Set → RSet
⟨ A ⟩ t = A

⟦_⟧ : RSet → Set
⟦ A ⟧ = ∀ {t} → (A t)

_+_ : Time → ℕ → Time
t + n = (t +ₙ n)

Signal : Set → Set
Signal (A) = Time → A

t0 : Time
t0 = 0

t1 : Time 
t1 = 1

data button : Set where
  up   : button
  down : button

data mbs : Time → Set where
  up   : (t : Time) → mbs (t)
  down : (t : Time) → mbs (t + 1) 

sts : Time → Set
sts t = mbs t

mbs1 : RSet
mbs1 t = mbs t

st : Time → button
st 0 = up
st (suc n) = down

--_[_,_] : RSet → Time → Time → Set
--A [ s , u ] = ∀ {t} → s ≤ t → t ≤ u → A t

--mouseButton : ⟦ ⟨ MouseButtonState ⟩ ⟧
--mouseButton = ?

-- button : Set
-- button = Signal b

-- mouseState : ⟦ ⟨ b ⟩ ⟧
-- mouseState = up

-- mouseState2 : ⟦ ⟨ b ⟩ ⟧
-- mouseState2 = down

-- sig : Signal b
-- sig t0 = up

-- ms : Time → b
-- ms zero = up
-- ms (suc t) = down



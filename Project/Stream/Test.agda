module Stream.Test where

open import Stream.Stream
open import Data.Vec hiding (_⋎_)
open import Data.Bool
open import Data.Nat
open import Data.Product
open import Relation.Binary.PropositionalEquality as P
open import Level renaming (suc to lsuc)
open import Stream.StreamEq

-- Teststreams

tts ffs : Stream Bool
tts = repeat true
ffs = repeat false

xxs : Stream Bool
xxs = repeat true

--0,1..
nats : Stream ℕ
hd nats = 0
tl nats = toStr suc

--1,2..
nats1 : Stream ℕ
nats1 = toStr suc

altBool : Stream Bool
altBool = tts ⋎ ffs

mutual
  evens : ∀ {i}{A : Set} → Stream A → Stream {i} A
  hd (evens x) = hd x
  tl (evens x) = odds (tl x)

  odds : ∀ {i A} → Stream A → Stream {i} A
  odds s = evens (tl s)


-- Tests

test : tts  ≡ₛ xxs
hd≡ test = refl
tl≡ test = test

vB : Data.Vec.Vec Bool 1
vB = true ∷ []

yys : Stream Bool
yys = vB ++ₛ (repeat true)

-- fails on tail
--test2 : tts ≡ₛ yys
--hd≡ test2 = refl
--tl≡ test2 = {!test2!}

¬s : Stream Bool → Stream Bool
hd (¬s s) = not (hd s)
tl (¬s s) = ¬s (tl s)

test4 : tts ≡ₛ (¬s ffs)
hd≡ test4 = refl
tl≡ test4 = test4

form1 : (ℕ × Stream ℕ) 
form1 = str-out nats1

form2 : (ℕ × Stream ℕ)
form2 = str-out (m suc nats)

-- 1,2,3
gen1 : ℕ → ℕ × ℕ
gen1 = (λ x → x , (suc x))

lem1 : Stream ℕ
lem1 = corec gen1 (1)

-- 1,2,3
gen2 : ℕ → ℕ × ℕ
gen2 = λ x → (x + 1) , (suc x) 

lem2 : Stream ℕ
lem2 = corec gen2 (0)

foldₛ : Stream ℕ → (ℕ → ℕ × ℕ)
proj₁ (foldₛ s n) = hd s
proj₂ (foldₛ s n) = hd (tl s)

eq! : lem1 ≡ₛ lem2
eq! = ∃-Bisim {!!} {!!} {!!} {!!} {!!}

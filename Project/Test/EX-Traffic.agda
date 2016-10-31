module Stream.Test.EX-Traffic where

open import Stream.Stream
open import Stream.RSet
open import Data.Bool
open import Data.Nat
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Product
open import Data.List
open import Relation.Nullary 
open import Data.Vec hiding (_⋎_) renaming (_∷_ to _▸_)

data TLight : Set where
  green : TLight
  red   : TLight

switch : TLight → TLight
switch green = red
switch red = green

switchₛ : Stream TLight → Stream TLight
switchₛ = lift1 switch
swS = switchₛ

nextT : Stream TLight → Stream TLight
nextT s = switchₛ (hd s ▸ tl s)

isRed : Stream TLight → RSet
isRed x = x ≡ₛ red ▸⋯  

check : (t1 t2 : TLight) → Bool
check green green = true
check green red = false
check red green = false
check red red = true

isWhat : Stream TLight → Stream TLight → RSet
isWhat x y = if same then (x ≡ₛ y) else ⊥ ▸⋯
  where same = check (hd x) (hd y)

hasState : Stream TLight → RSet
hasState x = x ≡ₛ x 
 
isGreen : Stream TLight → RSet
isGreen x = x ≡ₛ green ▸⋯  

switches : Stream TLight → RSet
switches x = isRed x →ₛ ○ (isGreen x)

notₛ : RSet → Set
notₛ = λ x → ⊥
--n = notₛ

n_ : RSet → Set
n R = ⊥

NS OW : Stream TLight
NS = corec (λ x → x , switch x) green
OW = nextT NS

--sequenceR : Stream TLight → Stream TLight
--sequenceR t s = t (s + 2)

--a1 a2 : Stream TLight
--a1 = λ x → green
--a2 = λ x → red

--_▹_ : ∀ {i : Size} {j : Size< i} -> TLight -> Stream {i} TLight -> Stream {j} TLight
--(a ▹ s) zero = a
--(a ▹ s) (suc n) = s n

-- howTo: t1 depend on t0! 
record rTLight : Set₁ where
  constructor r
  coinductive
  field
    t0 : Stream TLight 
    t1 : Stream TLight
open rTLight

{-# TERMINATING #-}
--am0 am1 am3 : Stream TLight
--am0 = green ▹ am3
--am1 = green ▹ (λ x → red)
--am3 = red ▹ am0

--am2 : TLight → Stream TLight
--am2 a = a ▹ (λ x → switch a)

prop : RSet
prop = (green ▸⋯) ≡ₛ (green ▸⋯ )

proof : ⟦ prop ⟧
now proof = refl
later proof = proof

-- --Todo
{-

-- a1 : gerade Zeiten green
-- a2 : ungerade zeiten green
-- ------------------------
-- (Beweis prop1 wird nicht klappen, aber prop2)
-- (Beweis fuer prop2: case)
-- ------------------------
-- - Diamond & Box to RSet
-- -----------------------
-- jede ampel wird mal wieder green (diamond green)


switch : RSet → RSet
switch s = ¬ₛ s 

-}

TTC : Stream Bool
TTC = corecc (λ x → x) (λ x → x) true

BBC : Bool → Stream Bool
BBC x = corecc (λ x → x) (λ x → (not x)) x

data am : Set where
  green : am
  red   : am

fun : Bool → am
fun false = red
fun true = green

swit : am → am
swit green = red
swit red = green

BBC' : (f : Bool → am) → Bool → Stream am
BBC' f b  = corecc f not b

stA1 stA2 : Stream TLight
stA1 = ⟨ green ▸ red ⟩ ▸⋯
stA2 = ⟨ red ▸ green ⟩ ▸⋯



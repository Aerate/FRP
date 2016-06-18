module Stream where

open import Size
open import Relation.Nullary
open import Relation.Binary
open import Data.Nat
open import Data.Vec renaming (_∷_ to _◂_)

record Stream {i : Size} {a} (A : Set a) : Set a where
  coinductive
  constructor _∷_
  field
    hd : A
    tl : ∀ {j : Size< i} → Stream {j} A

open Stream public; S = Stream
infixr 5 _∷_

tl' : ∀ {a} {A : Set a} → Stream A → Stream A
tl' s = tl s {∞}

δ : ∀ {a} {A : Set a} → ℕ → Stream A → Stream A
δ 0       s = s
δ (suc n) s = δ n (tl s)

repeat : ∀{a} {A : Set a} → A → Stream A
hd (repeat a) = a
tl (repeat a) = repeat a

takeₛ : ∀ {a} {A : Set a} (n : ℕ) (s : Stream A) → Vec A n
takeₛ 0 xs = []
takeₛ (suc n) xs = hd xs ◂ takeₛ n (tl xs)
t = takeₛ

mapₛ : ∀ {a i} {A B : Set a} (f : A → B) (s : Stream {i} A) → Stream {i} B
hd (mapₛ f s) = f (hd s)
tl (mapₛ f s) = mapₛ f (tl s)
m = mapₛ

toStr : ∀ {a} {A : Set a} → (ℕ → A) → Stream A
hd (toStr f) = f 0
tl (toStr f) = toStr (λ n → f (suc n))

_at_ : ∀ {a} {A : Set a} → Stream A → ℕ → A
s at n = hd (δ n s)

_++ˢ_ : ∀ {a} {A : Set a} {n : ℕ} → Vec A n → Stream A → Stream A
[]       ++ˢ s = s
(a ◂ as) ++ˢ s = a ∷ (as ++ˢ s)

_⋎ₛ_ :  ∀ {a} {A : Set a} → (s1 s2 : Stream A) → Stream A 
hd (s1 ⋎ₛ s2) = hd s1
tl (s1 ⋎ₛ s2) = s2 ⋎ₛ (tl s1)
_i_ = _⋎ₛ_ 

-----------------------
-- Set → Set Functions
-----------------------

⟨_⟩  : Set → Stream Set
hd ⟨ x ⟩ = x
tl ⟨ x ⟩ = ⟨ x ⟩

⟦_⟧ : Stream Set → Set
⟦ S ⟧ = ∀ {n : ℕ} → S at n

¬ₛ_ : Stream Set → Stream Set
hd (¬ₛ s) = ¬ (hd s)
tl (¬ₛ s) = ¬ₛ (tl s)
not = ¬ₛ_

--opt.
--iso : {A : Set} → A → A ≡ ⟦ ⟨ A ⟩ ⟧

-- opt.
-- cycleₛ : Set → Stream Set

------------------------
--- motivated by hbasold
--- https://github.com/hbasold/agda-stdlib/blob/master/src/Codata/Stream.agda
------------------------

module Bisimilarity {ℓ} (S : Setoid ℓ ℓ) where
  infix 4 _~_

  open Setoid S renaming (Carrier to A; isEquivalence to S-equiv)
  module SE = IsEquivalence S-equiv

  -- Stream equality is bisimilarity
  record _~_ {i : Size} (s t : Stream A) : Set ℓ where
    coinductive
    field
      hd≈ : hd s ≈ hd t
      tl~ : ∀ {j : Size< i} → _~_ {j} (tl s) (tl t)
  open _~_ public

-----------------------------
-- Examples of simple Streams
-----------------------------

module StreamEx where
  
  nats : Stream ℕ
  nats = 0 ∷ toStr suc

  S0 : Stream ℕ
  S0 = repeat 0

  S1 : Stream ℕ
  S1 = repeat 1

  Si : Stream ℕ
  Si = S0 i S1

  natsFrom : ℕ → Stream ℕ
  hd (natsFrom n) = n
  tl (natsFrom n) = natsFrom (suc n)

{- {-# OPTIONS --copatterns #-}
   {-# OPTIONS --sized-types #-}
-}

module Stream where

open import Size
open import Data.Nat renaming (compare to comp)
open import Data.Vec renaming (_∷_ to _◂_)
                     hiding (_⋎_)
infixr 5 _∷_
record Stream {i : Size} {a} (A : Set a) : Set a where
  coinductive
  constructor _∷_
  field
    hd : A
    tl : ∀ {j : Size< i} → Stream {j} A
open Stream public; S = Stream 

-- hd = headₛ ; tl = tailₛ -- can't use alias for pattern matching

-- nats = toStr suc
toStr : ∀ {a} {A : Set a} → (ℕ → A) → Stream A
hd (toStr f) = f 0
tl (toStr f) = toStr (λ n → f (suc n)) 

dropₛ : ∀ {a} {A : Set a} → ℕ → Stream A → Stream A
dropₛ 0       s = s
dropₛ (suc n) s = dropₛ n (tl s)

takeₛ : ∀ {a} {A : Set a} (n : ℕ) → Stream A → Vec A n
takeₛ 0 xs = []
takeₛ (suc n) xs = hd xs ◂ takeₛ n (tl xs)

repeat : ∀ {a} {A : Set a} → A → Stream A
hd (repeat a) = a
tl (repeat a) = repeat a

-- index
_at_ : ∀ {a} {A : Set a} → Stream A → ℕ → A
s at n = hd (dropₛ n s)

mapₛ : ∀ {a i} {A B : Set a} (f : A → B) (s : Stream {i} A) → Stream {i} B
hd (mapₛ f s) = f (hd s)
tl (mapₛ f s) = mapₛ f (tl s)
 
--prepend Vector to Stream
_++ₛ_ : ∀ {a} {A : Set a} {n : ℕ} → Vec A n → Stream A → Stream A
[]       ++ₛ s = s
(a ◂ as) ++ₛ s = a ∷ (as ++ₛ s)

--interleave streams
_⋎_ :  ∀ {a} {A : Set a} → (s1 s2 : Stream A) → Stream A 
hd (s1 ⋎ s2) = hd s1
tl (s1 ⋎ s2) = s2 ⋎ (tl s1)


module Stream.Stream where

open import Size
open import Data.Nat 
open import Data.Vec hiding (_⋎_)
open import Data.Product
open import Util

infix 4 ⟨_⟩▸⋯ _▸⋯
infixl 6 _▸
infix 7 _▸_
infixr 5  _►_ 

record Stream {i : Size} {a} (A : Set a) : Set a where
  coinductive
  constructor _►_
  field
    hd : A
    tl : ∀ {j : Size< i} → Stream {j} A
open Stream public; S = Stream 

--ℕ
toStr : ∀ {a} {A : Set a} → (ℕ → A) → Stream A
hd (toStr f) = f 0
tl (toStr f) = toStr (λ n → f (suc n)) 

--drop
dropₛ : ∀ {a} {A : Set a} → ℕ → Stream A → Stream A
dropₛ 0       s = s
dropₛ (suc n) s = dropₛ n (tl s)
d = dropₛ 

--take
takeₛ : ∀ {a} {A : Set a} (n : ℕ) → Stream A → Vec A n
takeₛ 0 xs = []
takeₛ (suc n) xs = hd xs ∷ takeₛ n (tl xs)
t = takeₛ

--index
_at_ : ∀ {a} {A : Set a} → Stream A → ℕ → A
s at n = hd (dropₛ n s)

--map
mapₛ : ∀ {i a} {A B : Set a} (f : A → B) (s : Stream {i} A) → Stream {i} B
hd (mapₛ f s) = f (hd s)
tl (mapₛ {i} f s) {j} = mapₛ {j} f (tl s {j})
m = mapₛ
 
--prepend 
_++ₛ_ : ∀ {a} {A : Set a} {n : ℕ} → Vec A n → Stream A → Stream A
[]       ++ₛ s = s
(a ∷ as) ++ₛ s = a ► (as ++ₛ s)

--interleave 
_⋎_ :  ∀ {a} {A : Set a} → (s1 s2 : Stream A) → Stream A 
hd (s1 ⋎ s2) = hd s1
tl (s1 ⋎ s2) = s2 ⋎ (tl s1)

--stream of products
_timesₛ_ : ∀ {a} {A : Set a} → (s1 s2 : Stream A) → Stream (A × A) 
hd (s1 timesₛ s2) = (hd s1) , (hd s2)
tl (s1 timesₛ s2) = (tl s1) timesₛ (tl s2)

--stream of products
_timesₛ'_ : ∀ {a} {A B : Set a} → (s1 : Stream A) → (s2 : Stream B) → Stream (A × B) 
hd (s1 timesₛ' s2) = (hd s1) , (hd s2)
tl (s1 timesₛ' s2) = (tl s1) timesₛ' (tl s2)

--coalgebra
str-out : ∀ {a} {A : Set a} → Stream A → A × Stream A
str-out s = (hd s) , tl s

--corecursion
corec : ∀ {a} {A X : Set a} → (X → A × X) → (∀ {i} → X → Stream {i} A)
hd (corec f x) = proj₁ (f x)
tl (corec f x) = corec f (proj₂ (f x))

_fby_ : ∀ {a} {A : Set a} → (s1 s2 : Stream A) → Stream A 
hd (s1 fby s2) = hd s1
tl (s1 fby s2) = s2

--constant
_▸⋯  : ∀ {a} {A : Set a} → A → Stream A
hd (x ▸⋯ ) = x
tl (x ▸⋯ ) = x ▸⋯  
repeat = _▸⋯ 

--pretty vec reading
_▸_ : ∀ {a} {A : Set a} → A → A → Vec A 2
a ▸ b = a ∷ b ∷ []

--pretty constant alias
_▸ : ∀ {a} {A : Set a} → A → Stream A
x ▸ = x ▸⋯

--Vec to Stream
⟨_⟩▸⋯  : ∀ {a n} {A : Set a} → Vec A (suc n) → Stream A
⟨ xs ⟩▸⋯ = aux xs []
  where aux : ∀ {a n m} {A : Set a} → Vec A (suc n) → Vec A m → Stream A
        hd (aux keep (x ∷ count)) = x
        tl (aux keep (x ∷ count)) = aux keep count
        hd (aux (v ∷ vs) []) = v
        tl (aux (v ∷ vs) []) = aux (v ∷ vs) vs

---------------------------
-- Function Lifting 
---------------------------

lift0 = _▸⋯ 

lift1 = mapₛ

lift2 :  ∀ {a b c i} {A : Set a} {B : Set b} {C : Set c} (f : A → B → C) (s : Stream {i} A) (t : Stream {i} B) → Stream {i} C
hd (lift2 f as bs) = f (hd as) (hd bs)
tl (lift2 f as bs) = lift2 f ((tl as)) ((tl bs))


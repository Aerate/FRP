module Stream.Stream where

open import Size
open import Data.Nat 
open import Data.Vec renaming (_∷_ to _◂_) hiding (_⋎_)
open import Data.Product

infixr 5 _∷_
record Stream {i : Size} {a} (A : Set a) : Set a where
  coinductive
  constructor _∷_
  field
    hd : A
    tl : ∀ {j : Size< i} → Stream {j} A
open Stream public; S = Stream 

--lift ℕ
toStr : ∀ {a} {A : Set a} → (ℕ → A) → Stream A
hd (toStr f) = f 0
tl (toStr f) = toStr (λ n → f (suc n)) 

--lift Set
toStr' : ∀ {a} {A : Set a} {B : Set a} → A → (A → B) → Stream B
hd (toStr' a f) = f a
tl (toStr' a f) = toStr' (f a) (λ z → z)

--drop
dropₛ : ∀ {a} {A : Set a} → ℕ → Stream A → Stream A
dropₛ 0       s = s
dropₛ (suc n) s = dropₛ n (tl s)
d = dropₛ 

--take
takeₛ : ∀ {a} {A : Set a} (n : ℕ) → Stream A → Vec A n
takeₛ 0 xs = []
takeₛ (suc n) xs = hd xs ◂ takeₛ n (tl xs)
t = takeₛ

--constant
repeat : ∀ {a} {A : Set a} → A → Stream A
hd (repeat a) = a
tl (repeat a) = repeat a

--index
_at_ : ∀ {a} {A : Set a} → Stream A → ℕ → A
s at n = hd (dropₛ n s)

--map
mapₛ : ∀ {a i} {A B : Set a} (f : A → B) (s : Stream {i} A) → Stream {i} B
hd (mapₛ f s) = f (hd s)
tl (mapₛ f s) = mapₛ f (tl s)
m = mapₛ
 
--prepend 
_++ₛ_ : ∀ {a} {A : Set a} {n : ℕ} → Vec A n → Stream A → Stream A
[]       ++ₛ s = s
(a ◂ as) ++ₛ s = a ∷ (as ++ₛ s)

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

--coalgebra (HB) (/ fold?)
str-out : ∀ {a} {A : Set a} → Stream A → A × Stream A
str-out s = (hd s) , tl s

--corecorsion (/ unfold?)
corec : ∀ {a} {A X : Set a} → (X → A × X) → (∀ {i} → X → Stream {i} A)
hd (corec f x) = proj₁ (f x)
tl (corec f x) = corec f (proj₂ (f x))


---------------------------
-- functions of Stream ℕ
---------------------------

--addition on streams ℕ
_⊕_ : ∀ {i} → Stream {i} ℕ → Stream {i} ℕ → Stream {i} ℕ
hd (x ⊕ y) = hd x + hd y
tl (x ⊕ y) = tl x ⊕ tl y


-- ---------------------------
-- -- Stream primitives of MM
-- ---------------------------

-- lift0 = repeat

-- lift1 = mapₛ

-- lift2 :  ∀ {a i} {A B C : Set a} (f : A → B → C) (s : Stream {i} A) (t : Stream {i} B) → Stream {i} C
-- hd (lift2 f as bs) = f (hd as) (hd bs)
-- tl (lift2 f as bs) = lift2 f ((tl as)) ((tl bs))

-- sPair = _timesₛ_

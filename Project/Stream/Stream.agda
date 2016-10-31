module Stream.Stream where

open import Level renaming (suc to lsuc)
open import Size
open import Data.Nat hiding (_⊔_)
open import Data.Vec hiding (_⋎_) renaming (_∷_ to _▸_)
open import Data.Product
open import Util
open import Data.List

infix 3 ⟨_▸⋯ _▸⋯
infixr 5  _▸_ 

-- coinductively defined parametric Streams annotated by sizes
record Stream {i : Size} {a} (A : Set a) : Set a where
  coinductive
  constructor _▸_
  field
    hd : A
    tl : ∀ {j : Size< i} → Stream {j} A
open Stream public; S = Stream 

--constant
_▸⋯  : ∀ {a} {A : Set a} → A → Stream A 
hd (x ▸⋯ ) = x
tl (x ▸⋯ ) = x ▸⋯  
repeat = _▸⋯ 

--ℕ
toStr : ∀ {a} {A : Set a} → (ℕ → A) → Stream A
hd (toStr f) = f 0
tl (toStr f) = toStr (λ n → f (suc n)) 

--drop
dropₛ : ∀ {a} {A : Set a} → ℕ → Stream A → Stream A
dropₛ 0       s = s
dropₛ (suc n) s = dropₛ n (tl s)

--take
takeₛ : ∀ {a} {A : Set a} (n : ℕ) → Stream A → Vec A n
takeₛ 0 xs = []
takeₛ (suc n) xs = hd xs ▸ takeₛ n (tl xs)

--index
_at_ : ∀ {a} {A : Set a} → Stream A → ℕ → A
s at n = hd (dropₛ n s)

--map
mapₛ : ∀ {i a b} {A : Set a} {B : Set b} (f : A → B) (s : Stream {i} A) → Stream {i} B
hd (mapₛ f s) = f (hd s)
tl (mapₛ {i} f s) {j} = mapₛ {j} f (tl s {j})
 
--prepend Vector
_++ₛ_ : ∀ {a} {A : Set a} {n : ℕ} → Vec A n → Stream A → Stream A
[]       ++ₛ s = s
(a ▸ as) ++ₛ s = a ▸ (as ++ₛ s)

--interleave 
_⋎_ :  ∀ {a} {A : Set a} → (s1 s2 : Stream A) → Stream A 
hd (s1 ⋎ s2) = hd s1
tl (s1 ⋎ s2) = s2 ⋎ (tl s1)

_fby_ : ∀ {a} {A : Set a} → (s1 s2 : Stream A) → Stream A 
hd (s1 fby s2) = hd s1
tl (s1 fby s2) = s2

-- coalgebra
str-out : ∀ {a} {A : Set a} → Stream A → A × Stream A
str-out s = (hd s) , tl s

--corecursion
corec : ∀ {a} {A X : Set a} → (X → A × X) → (∀ {i} → X → Stream {i} A)
hd (corec f x) = proj₁ (f x)
tl (corec f x) = corec f (proj₂ (f x))

corec' : ∀ {X A : Set} → (X → A) → (X → X) → (X → Stream A)
hd (corec' h s x) = h x
tl (corec' h s x) = corec' h s (s x)

str-out' : ∀ {a i} {A X : Set a} → (Stream {i} A) → (X → A × X)
str-out' s x = (hd s) , x

-- repeat a given Vector (cycle) 
⟨_▸⋯ : ∀ {a n} {A : Set a} → Vec A (suc n) → Stream A
⟨ xs ▸⋯ = aux xs []
  where aux : ∀ {a n m} {A : Set a} → Vec A (suc n) → Vec A m → Stream A
        hd (aux keep (x ▸ count)) = x
        tl (aux keep (x ▸ count)) = aux keep count
        hd (aux (v ▸ vs) []) = v
        tl (aux (v ▸ vs) []) = aux (v ▸ vs) vs

infix 7 _⟩ 
_⟩ : ∀ {A : Set} → A → Vec A 1 
a ⟩ = a ▸ []

---------------------------
-- Function Lifting 
---------------------------

lift0 = _▸⋯ 

lift1 = mapₛ

lift2 :  ∀ {a b c i} {A : Set a} {B : Set b} {C : Set c} (f : A → B → C) (s : Stream {i} A) (t : Stream {i} B) → Stream {i} C
hd (lift2 f as bs) = f (hd as) (hd bs)
tl (lift2 f as bs) = lift2 f ((tl as)) ((tl bs))

---------------------------
-- Views
---------------------------

data Any {a p} {A : Set a} (P : A → Set p) : Stream A → Set (a ⊔ p) where
  here  : ∀ {s} (px : P (hd s)) → Any P s
  there : ∀ {s} (ps : Any P (tl s)) → Any P s

record All {a p} {A : Set a} (P : A → Set p) (s : Stream A) : Set (a ⊔ p) where
  coinductive
  field
    ✓-head : P (hd s)
    ✓-tail : All P (tl s)
open All public

takeUntil : ∀ {a p} {A : Set a} {P : A → Set p} → (s : Stream A) → Any P s → List A × Stream A
takeUntil         s (here  px)  = [] , s
takeUntil {A = A} s (there any) = hd s ∷ (proj₁ p) , proj₂ p
  where
    p : List A × Stream A
    p = takeUntil (tl s) any

---------------------------
-- Aliases
---------------------------

d = dropₛ 
t = takeₛ
m = mapₛ

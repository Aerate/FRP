------------------------------------------------------------------------
-- R⋯⟩ 
--
-- Streams as infinite lists that can be parametrized over Sets
------------------------------------------------------------------------
module Stream.Stream where

open import Level renaming (suc to ℓ⁺; zero to ℓ₀) public
open import Size public
open import Data.Nat hiding (_⊔_)
open import Data.Vec renaming (_⋎_ to _⋎⋎_ ; _∷_ to _▸_; take to vtake; drop to vdrop; map to vmap) public
open import Data.Product hiding (map)
open import Data.Bool
open import Data.List renaming (drop to ldrop; take to ltake; map to lmap)
open import Function

infix 6  _▸⋯
infixr 5  _▸_ 

-- The type of coinductively defined streams with annotated sizes
--
-- copatterns serve double duty:
-- the first element of a stream may be extracted by hd
-- while tl extracts the substream after head

record Stream {i : Size} {a : Level} (A : Set a) : Set a where
  coinductive
  constructor _▸_
  field
    hd : A
    tl : ∀ {j : Size< i} → Stream {j} A
open Stream public 

-- streams of constant value
_▸⋯  : ∀ {a} {A : Set a} → A → Stream A 
hd (x ▸⋯ ) = x
tl (x ▸⋯ ) = x ▸⋯  

-- streams derived from a function
toStr : ∀ {a} {A : Set a} → (A → A) → A → Stream A
hd (toStr f a) = a
tl (toStr f a) = toStr f (f a)

-- drop n elements
drop : ∀ {a} {A : Set a} → ℕ → Stream A → Stream A
drop 0       s = s
drop (suc n) s = drop n (tl s)

-- take n elements and present the result as a vector of length n
take : ∀ {a} {A : Set a} (n : ℕ) → Stream A → Vec A n
take 0 xs = []
take (suc n) xs = hd xs ▸ take n (tl xs)

-- indexing
_at_ : ∀ {a} {A : Set a} → Stream A → ℕ → A
s at n = hd (drop n s)

-- mapping
map : ∀ {i a b} {A : Set a} {B : Set b} (f : A → B) (s : Stream {i} A) → Stream {i} B
hd (map f s) = f (hd s)
tl (map {i} f s) {j} = map {j} f (tl s {j})
 
-- adds a vector as prefix to a stream
_++ₛ_ : ∀ {a} {A : Set a} {n : ℕ} → Vec A n → Stream A → Stream A
[]       ++ₛ s = s
(a ▸ as) ++ₛ s = a ▸ (as ++ₛ s)

-- interleave two streams
_⋎_ :  ∀ {a} {A : Set a} → (s1 s2 : Stream A) → Stream A 
hd (s1 ⋎ s2) = hd s1
tl (s1 ⋎ s2) = s2 ⋎ (tl s1)

-- coalgebra / folding a stream
str-out : ∀ {a} {A : Set a} → Stream A → A × Stream A
str-out s = (hd s) , tl s

-- corecursion / unfolding a stream
corec : ∀ {a} {A X : Set a} → (X → A × X) → (∀ {i} → X → Stream {i} A)
hd (corec f x) = proj₁ (f x)
tl (corec f x) = corec f (proj₂ (f x))

--corec' : ∀ {X A : Set} → (X → A) → (X → X) → (X → Stream A)
--hd (corec' h s x) = h x
--tl (corec' h s x) = corec' h s (s x)

--str-out' : ∀ {a i} {A X : Set a} → (Stream {i} A) → (X → A × X)
--str-out' s x = (hd s) , x

-- applicative mapping
_<*>_ : ∀ {X A : Set} → Stream (X → A) → Stream X → Stream A
hd (fs <*> ss) = hd fs (hd ss)
tl (fs <*> ss) = (tl fs) <*> (tl ss)

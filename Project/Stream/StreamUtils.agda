------------------------------------------------------------------------
--
-- Utilities for Streams
--
------------------------------------------------------------------------
module Stream.StreamUtils where

open import Data.Nat hiding (_⊔_)
open import Data.Product hiding (map)
open import Data.List renaming (drop to ldrop; take to ltake; map to lmap)
open import Function

open import Stream.Stream

infix 6 ⟨_▸⋯
infix 7 _⟩

---------------------------------------------------
-- Functor and applicative instance
-- Note: None of the laws are currently implemented
----------------------------------------------------

-- applicative mapping
_<*>_ : ∀ {X A : Set} → Stream (X → A) → Stream X → Stream A
hd (fs <*> ss) = hd fs (hd ss)
tl (fs <*> ss) = (tl fs) <*> (tl ss)

record Functor (F : Set → Set) : Set₁ where
  field
    fmap : ∀ {X A} → (X → A) → F X → F A
open Functor {{...}} public

record Applicative (F : Set → Set) : Set₁ where
  infixl 2 _✴_
  field
    pure : ∀ {X} → X → F X
    _✴_  : ∀ {X A} → F (X → A) → F X → F A
  applicativeFunctor : Functor F
  applicativeFunctor = record {fmap = _✴_ ∘ pure}
open Applicative {{...}} public

applicativeStream : Applicative (λ X → Stream X)
applicativeStream = record { pure = _▸⋯  ; _✴_ = _<*>_ }

FunctorStream : Functor (λ X → Stream X)
FunctorStream = record { fmap = map }

---------------------------
-- Function lifting
---------------------------

-- nullary
lift0 = _▸⋯

-- unary
lift1 = map

-- binary
lift2 :  ∀ {a b c i} {A : Set a} {B : Set b} {C : Set c} (f : A → B → C) (s : Stream {i} A) (t : Stream {i} B) → Stream {i} C
hd (lift2 f as bs) = f (hd as) (hd bs)
tl (lift2 f as bs) = lift2 f ((tl as)) ((tl bs))

---------------------------
-- Views on streams
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

repeat = _▸⋯

---------------------------
-- Helpers
---------------------------

-- repeat a given vector, with prefix
_∷⟨_▸⋯ : ∀ {a n m} {A : Set a} → Vec A m → Vec A (suc n) → Stream A
hd ((x ▸ count) ∷⟨ keep ▸⋯ ) = x
tl ((x ▸ count) ∷⟨ keep ▸⋯ ) = count ∷⟨ keep ▸⋯
hd ([] ∷⟨ (v ▸ vs) ▸⋯) = v
tl ([] ∷⟨ (v ▸ vs) ▸⋯) = vs ∷⟨ (v ▸ vs) ▸⋯


-- repeat a given vector (alias cycle), without prefix
⟨_▸⋯ : ∀ {a n} {A : Set a} → Vec A (suc n) → Stream A
⟨ xs ▸⋯ = [] ∷⟨ xs ▸⋯

-- allows for sugaring a vector in combination with cycle
_⟩ : ∀ {a} {A : Set a} → A → Vec A 1
a ⟩ = a ▸ []


-- prefix a vector to a stream
_prefix_ : ∀ {a n} {A : Set a} → Vec A n → Stream A → Stream A
[] prefix as = as
(x ▸ v) prefix as = x ▸ (v prefix as)

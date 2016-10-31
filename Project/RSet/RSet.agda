module RSet.RSet where

open import Size
open import Data.Empty
open import Data.Unit
open import Data.Vec
open import Data.Nat
open import Data.Fin
open import Stream.Stream
open import Data.Product
open import Data.Sum
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Core
open import Function

infix 2 _≡ₛ_
infixr 2 ¬ₛ_
--infix 4 --⟨_⟩▹⋯ --_▹⋯
infix 7 _▹_

RSet : ∀ {i} → Set₁
RSet {i} = Stream {i} Set

record ⟦_⟧ (R : RSet) : Set where 
  coinductive
  constructor _►_   
  field
    now   : hd R 
    later : ⟦ tl R ⟧
open ⟦_⟧ public

--⟪_⟫ : Set → RSet
--hd ⟪ A ⟫ = A
--tl ⟪ A ⟫ = ⟪ A ⟫ 

data ⟪_⟫ : {n : ℕ} (V : Vec Set n) → Set where
  []  : ⟪ [] ⟫ 
  _▹_ : {n : ℕ} → {v : Vec Set (suc n)} → head v → ⟪ tail v ⟫ → ⟪ v ⟫ 

--⟨_▹⋯ : {n : ℕ} → {v : Vec Set (suc n)} → ⟪ v ⟫ → ⟦ ⟨ v ▸⋯ ⟧ 
--⟨ x ▹ xs ▹⋯ = (hd ({!origV!} ▸⋯)) ► {!!}
--  where origV : Set
--        origV = {!!}

reflect : ∀ {n} → Fin n → Fin n
reflect {suc n} zero = fromℕ n
reflect {suc n} (suc x) = Data.Fin.pred (suc (reflect x))

-- repeatProofVec  : ∀ {n} → {v : Vec Set (suc n)} → ⟪ v ⟫ → ⟦ ⟨ v ▸⋯ ⟧ 
-- repeatProofVec {n} {v} proofOfv  = aux proofOfv (fromℕ n) 
--     where aux : ∀ {n} → {v : Vec Set (suc n)} → ⟪ v ⟫ → Fin (suc n) → ⟦ ⟨ v ▸⋯ ⟧
--           now (aux proofOfv zero) = lookup (reflect zero) {!!}
--           later (aux proofOfv zero) = {!!}
--           now (aux proofOfv (suc k)) = {!!}
--           later (aux proofOfv (suc k)) = {!!}

-- ⟨_▹⋯ = repeatProofVec 

-- repeatProofVec2  : ∀ {n} → {v : Vec Set (suc n)} → ⟪ v ⟫ → ⟦ ⟨ v ▸⋯ ⟧ 
-- repeatProofVec2 (x ▹ xs) = {!!}

¬ₛ_ : RSet → RSet
¬ₛ_ = mapₛ ¬_
ns_ = ¬ₛ_

_×ₛ_ : RSet → RSet → RSet
_×ₛ_ = lift2 _×_

_⊎ₛ_ : RSet → RSet → RSet
_⊎ₛ_ = lift2 _⊎_

_→ₛ_ : RSet → RSet → RSet
_→ₛ_ = lift2 f where 
  f : Set → Set → Set
  f A B = A → B

_≡ₛ_ : ∀ {a} {A : Set a} → Stream A → Stream A → Stream (Set a)
_≡ₛ_ = lift2 _≡_

_≡ₐ_ : {A : Set} → Stream A → Stream A → RSet
_≡ₐ_ = lift2 _≡_

_≢ₛ_ : {A : Set} → Stream A → Stream A → RSet
_≢ₛ_ = lift2 _≢_

○ : ∀ {i : Size} → RSet → RSet
○ A = tl A

--◇ : ∀ {i : Size} → RSet → RSet
--◇ R = R ⊎ₛ (◇ (○ R))

-- bessere namen fuer konstruktoren, already / soon
data hd◇ (R : RSet) : Set where
  ◇-now   : (hd R) → hd◇ R
  ◇-later : (hd◇ (○ R)) → hd◇ R

record hd□ (R : RSet) : Set where
  inductive
  field
    □-now   : hd R
    □-later : hd□ (○ R)

□ : ∀ {i : Size} → RSet → RSet
hd (□ x) = hd□ x
tl (□ x) = □ (tl x)

--□ : ∀ {i : Size} → RSet → RSet
--hd (□ x) = ⟦ x ⟧
--tl (□ x) = □ (tl x)

◇ : ∀ {i : Size} → RSet → RSet
hd (◇ R) = hd◇ R
tl (◇ R) = ◇ (tl R)
eventually = ◇ 

--di-lemma : ∀ {R} → ⟦ (◇ (◇ R)) ⟧ ≡ ⟦ ◇ R ⟧
--di-lemma = {!!}

--□ : ∀ {i : Size} → RSet → RSet
--hd (□ A) = hd A
--tl (□ A) = □ (tl A)

-- R 'until' S
data _hdU_ (R S : RSet) : Set where
  finally : hd S → R hdU S
  _until_ : hd R → (○ R) hdU (○ S) → R hdU S

_U_ : RSet → RSet → RSet
hd (R U S) = R hdU S
tl (R U S) = (○ R) U (○ S)

Empty : RSet
Empty = repeat ⊥

--pretty vec reading
--_▹_ : Set → Set → Vec Set 2
--a ▹ b = a ∷ b ∷ []

-- ⟨_⟩▹⋯  : ∀ {i n} → Vec Set (suc n) → Stream {i} Set
-- ⟨ xs ⟩▹⋯ = aux xs []
--   where aux : ∀ {a n m} {A : Set a} → Vec A (suc n) → Vec A m → Stream A
--         hd (aux keep (x ∷ count)) = x
--         tl (aux keep (x ∷ count)) = aux keep count
--         hd (aux (v ∷ vs) []) = v
--         tl (aux (v ∷ vs) []) = aux (v ∷ vs) vs

-- _▹⋯  : {S : Set} → (s : S) → ⟦ S ▸⋯ ⟧
-- now (s ▹⋯) = s
-- later (s ▹⋯) = s ▹⋯


lift-lem : ∀ {la lb} {A : Set la} {B : Set lb} {C : Set} {f : A → B → C} {a : A} {b : B} → ⟦ (lift2 f (a ▸⋯ ) (b ▸⋯ )) ≡ₛ ((f a b) ▸⋯) ⟧
now lift-lem   = refl
later lift-lem = lift-lem  

-- 
--eq-lem : {A : Set} → (s t : Stream A) → ⟦ s ≡ₛ t ⟧ → s ≡ t
--eq-lem s t p = {!!}



-- lem
-- ⟦ s ≡ₛ t ⟧ → s ≡ t


--
-- isTrue TT = refl ▹⋯ 
-- 

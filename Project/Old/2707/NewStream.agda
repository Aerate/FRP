module NewStream where

open import Size
open import Data.Nat
open import Parity
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Product
open import Data.List
open import Data.Empty
open import Level renaming (zero to lzero ; suc to ↑ ; _⊔_ to _U_)

-- stream + size ohne level => zu n-term 


generalStream : {i : Size} {ℓ : Level} → (A : Set ℓ) → Set (ℓ)
generalStream A = ℕ → A 

RSet : Set₁
RSet = generalStream Set

Stream : Set → Set
Stream = generalStream

⟨_⟩ : Set → RSet
⟨ A ⟩ t = A

⟦_⟧ : RSet → Set
⟦ A ⟧ = ∀ {n} → A n

○ : RSet → RSet
○ A t = A (t + 1)

_≡ₛ_ : ∀ {A} → (s1 s2 : Stream A) → RSet
s1 ≡ₛ s2 = λ n → (s1 n ≡ s2 n)
_==_ = _≡ₛ_

const0 : Stream ℕ
const0 n = 0


-- in coind nachbauen
lemc0 : RSet
lemc0 = const0 ≡ₛ const0

--⟦ lemc0 ⟧ = ∀ {n} → A 0

proofLem : ⟦ lemc0 ⟧
proofLem = λ {n} → refl

head : ∀ {i ℓ A} → generalStream {i} {ℓ} A → A
head s = s zero

tail : ∀ {i ℓ A} {j : Size< i} → generalStream {i} {ℓ} A → generalStream {j} {ℓ} A
tail s = λ x → s (suc x)

--tail : ∀ {A} → Stream A → Stream A
--tail s = λ x → s (suc x)

takeₛ : ∀ {i ℓ A} → ℕ → generalStream {i} {ℓ} A → List {ℓ} A
takeₛ zero s = []
takeₛ (suc n) s = head s ∷ (takeₛ n (tail s))
t = takeₛ

const : ∀ {A} →  A → Stream A
const a = λ x → a

_at_ : ∀ {i ℓ A} → generalStream {i} {ℓ} A → ℕ → A
s at zero = head s
s at suc n = (tail s) at n

_▸_ : ∀ {i ℓ} {j : Size< i} {A : Set ℓ} → A -> generalStream {j} A -> generalStream {i} A
(a ▸ s) zero = a
(a ▸ s) (suc n) = s n

♭_ : ∀ {i} {A : Set} {j : Size< i} → generalStream {i} A → generalStream {j} A 
♭ s = s

cube : ℕ → ℕ
cube n = n * n * n

s0 : Stream ℕ
s0 = λ x → 0

s1 : Stream ℕ
s1 = 1 ▸ s0

s2 : Stream ℕ
s2 = suc

s3 : Stream ℕ
s3 = cube
------------------------------------------------------------
-- Lifts

--Level + 1 nötig? Weil l₂ als Output nicht klappt. Aber A → B gleicher Level ?
lift1 : ∀ {i} {l₁ l₂ : Level} {A B : Set l₁} → (A → B) → generalStream {i} {l₁} A → generalStream {i} {l₁} B 
lift1 f s = λ x → f (s x)

-- LEVEL: A B aus ℓ, 'gepackt' in generalStream, aber gleicher Level (Verständnis: ℓ bezieht sich auf A B, aber gS ist ℓ + 1 ?)
lift1-1 : ∀ {i} {ℓ} {A B : Set ℓ} → (A → B) → generalStream {i} {ℓ} A → generalStream {i} {ℓ} B 
lift1-1 f s = λ x → f (s x)

lift1-2 : ∀ {ℓ : Level} {A B : Set} → (A → B) → generalStream A → generalStream B 
lift1-2 f s = λ x → f (s x)

---------------------
lift2 : ∀ {l1 l2 l3} {A B C : Set} → (A → B → C) → generalStream {l1} A → generalStream {l2} B → generalStream {l3} C 
lift2 f s1 s2 = λ x → f (s1 x) (s2 x)

lift2-1 : ∀ {i} {a b} {A B : Set a} {C : Set (a Level.⊔ b)} → (A → B → C) → generalStream {i} {a} A → generalStream {i} {a} B → generalStream {i} {a U b} C 
lift2-1 f s1 s2 = λ x → f (s1 x) (s2 x)

-- LEVEL: A aus a, B aus b, f (A → B → C) 'nach' least upper bound von (a b)
-- SIZE: gleich bei allen Streams
lift2-2 : ∀ {i} {a b} {A : Set a} {B : Set b} {C : Set (a U b)} → (A → B → C) → generalStream {i} {a} A → generalStream {i} {b} B → generalStream {i} {a U b} C 
lift2-2 f s1 s2 = λ x → f (s1 x) (s2 x)

--
------------------------------------------------------------

¬ₛ_ : RSet → RSet
¬ₛ_ = lift1-1 ¬_ 

_×ₛ_ : RSet → RSet → RSet
_×ₛ_ = lift2-2 _×_

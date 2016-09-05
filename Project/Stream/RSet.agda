module Stream.RSet where

open import Size
open import Data.Empty
open import Data.Unit
open import Data.Vec
open import Data.Nat
open import Stream.Stream
open import Data.Product
open import Data.Sum
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Core

infix 3 _≡ₛ_
infixr 2 ¬ₛ_
infix 4 ⟨_⟩▹⋯ _▹⋯
infixl 6 _▹
infix 7 _▹_

RSet : ∀ {i} → Set₁
RSet {i} = Stream {i} Set

⟨_⟩ : Set → RSet
hd ⟨ A ⟩ = A
tl ⟨ A ⟩ = ⟨ A ⟩ 

⟪_⟫ : RSet → Set
⟪ x ⟫ = hd x

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

_≡ₛ_ : {A : Set} → Stream A → Stream A → RSet
_≡ₛ_ = lift2 _≡_

_≢ₛ_ : {A : Set} → Stream A → Stream A → RSet
_≢ₛ_ = lift2 _≢_

○ : ∀ {i : Size} → RSet → RSet
○ A = tl A

○ₙ : ∀ {i : Size} → RSet → Set
○ₙ A = hd (tl A)
next = ○ₙ

□ : ∀ {i : Size} → RSet → RSet
□ A = A

Empty : RSet
Empty = repeat ⊥

--constant
_▹⋯  : Set → RSet
hd (x ▹⋯ ) = x
tl (x ▹⋯ ) = x ▹⋯  

--pretty vec reading
_▹_ : Set → Set → Vec Set 2
a ▹ b = a ∷ b ∷ []

--pretty constant alias
_▹ : ∀ {i} → Set → Stream {i} Set
x ▹ = x ▹⋯

⟨_⟩▹⋯  : ∀ {i n} → Vec Set (suc n) → Stream {i} Set
⟨ xs ⟩▹⋯ = aux xs []
  where aux : ∀ {a n m} {A : Set a} → Vec A (suc n) → Vec A m → Stream A
        hd (aux keep (x ∷ count)) = x
        tl (aux keep (x ∷ count)) = aux keep count
        hd (aux (v ∷ vs) []) = v
        tl (aux (v ∷ vs) []) = aux (v ∷ vs) vs

record ⟦_⟧ (R : RSet) : Set where 
  coinductive
  constructor _►_   
  field
    now   : hd R 
    later : ⟦ tl R ⟧
open ⟦_⟧ public


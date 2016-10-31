module Stream.Semantics where

open import Size
open import Function
open import Stream.Stream
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Relation.Binary.PropositionalEquality

open import Stream.RSet

record _≈_ (A B : Set) : Set where
  constructor ≈ₑ 
  field
    f : A → B
    g : B → A
    invₗ : f ∘ g ≡ id
    invᵣ : g ∘ f ≡ id

embed : Bool → Set
embed true  = ⊤
embed false = ⊥

cont : Set → Set₁
cont B = (B → RSet) → RSet

_⊨_ : ∀ {B : Set} → (B → Stream Bool) → cont B → Set
(b ⊨ c) = hd (c ((lift1 embed) ∘ b))

-- scoped type variables in hs

atom : ∀ {B : Set} → B → cont B
atom b = λ g → (g b)

op : ∀ {B : Set} → (RSet → RSet) → cont B → cont B
op f c = f ∘ c

drop1 : ∀ {B : Set} → (B → Stream Bool) → (B → Stream Bool)
drop1 b = ((dropₛ 1) ∘ b) 

-- --semi-haendische reduktion zu NF :
-- hd (tl (c (λ x → mapₛ embed (b x)))) !≡! hd (c (λ x → mapₛ embed (tl (b x))))
-- c auch lesbar als {c : (B → Stream Set) → Stream Set}
sem-○ : ∀ {B : Set} (b : B → Stream Bool) (c : cont B) → ((drop1 b) ⊨ c) ≈ (b ⊨ (op ○ c))
_≈_.f (sem-○ b c) x = {!!}
_≈_.g (sem-○ b c) x = {!!}
_≈_.invₗ (sem-○ b c) = {!!}
_≈_.invᵣ (sem-○ b c) = {!!}

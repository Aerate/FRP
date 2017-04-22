module FStream.Core where

open import ContainerMonkeyPatched renaming (map to fmap)
open import Data.Nat hiding (_⊔_)
open import Data.Product hiding (map)
open import Data.Vec using ([]; _∷_; Vec)
open import Level hiding (suc)
open import Size public

mutual
  record FStream {i : Size} {ℓ₁ ℓ₂} (C : Container ℓ₁) (A : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
    inductive
    field
      inF : ⟦ C ⟧ (FStream' {i} C A)
  record FStream' {i : Size} {ℓ₁ ℓ₂} (C : Container ℓ₁) (A : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
    coinductive
    field
      head : A
      tail : {j : Size< i} → FStream {j} C A
open FStream
open FStream'

_►_ : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} {A : Set ℓ₂} → ⟦ C ⟧ A → FStream C A → FStream C A
inF (a ► as) = fmap (λ x → record { head = x ; tail = as }) a

mutual
  map : ∀ {i ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁} {A : Set ℓ₂} {B : Set ℓ₃} → (A → B) → FStream {i} C A → FStream {i} C B
  inF (map f as) = fmap (map' f) (inF as)

  map' : ∀ {i ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁} {A : Set ℓ₂} {B : Set ℓ₃} → (A → B) → FStream' {i} C A → FStream' {i} C B
  head (map' f as) = f (head as)
  tail (map' f as) = map f (tail as)


mutual
  constantly : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁} {A : Set ℓ₂} → ⟦ C ⟧ A → FStream {i} C A
  inF (constantly ca) = fmap (constantly' ca) ca

  constantly' : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁} {A : Set ℓ₂} → ⟦ C ⟧ A → A → FStream' {i} C A
  head (constantly' ca a) = a
  tail (constantly' ca a) = constantly ca


{-
repeat : {A : Set} → {C : Container Level.zero} → ⟦ C ⟧ A -> FStream C A
proj₁ (FStream.inF (repeat (proj₁ , proj₂))) = proj₁
FStream'.head (proj₂ (FStream.inF (repeat (proj₁ , proj₂))) x) = proj₂ x
FStream'.tail (proj₂ (FStream.inF (repeat ca)) x) = repeat ca
-}

mutual
  corec : ∀ {i ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁} {A : Set ℓ₂} {X : Set ℓ₃} → (X → A × ⟦ C ⟧ X) → ⟦ C ⟧ X → FStream {i} C A
  inF (corec f x) = fmap (corec' f) x

  corec' : ∀ {i ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁} {A : Set ℓ₂} {X : Set ℓ₃} → (X → A × ⟦ C ⟧ X) → X → FStream' {i} C A
  head (corec' f x) = proj₁ (f x)
  tail (corec' f x) = corec f (proj₂ (f x))

infix 8 _▻_
infixr 5 _▻'_
infix 6 ⟨_▻⋯
infix 7 _⟩

data FVec {ℓ₁ ℓ₂} (C : Container ℓ₁) (A : Set ℓ₂) : (n : ℕ) → Set (ℓ₁ ⊔ ℓ₂) where
  FNil : FVec C A 0
  FCons : ∀ {n} → ⟦ C ⟧ (A × FVec C A n) → FVec C A (suc n)

nest : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} {A : Set ℓ₂} {n} → Vec (⟦ C ⟧ A) n → FVec C A n
nest [] = FNil
nest (a ∷ as) = FCons (fmap (λ x → x , nest as) a)

_▻_ :  ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} {A : Set ℓ₂} {n} → A → ⟦ C ⟧ (FVec C A n) → FVec C A (suc n)
a ▻ v = FCons (fmap (λ x → a , x) v)
_▻'_ :  ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} {A : Set ℓ₂} {n} → ⟦ C ⟧ A → (FVec C A n) → FVec C A (suc n)
a ▻' v = FCons (fmap (λ x → x , v) a)

_⟩ : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} {A : Set ℓ₂} → ⟦ C ⟧ A → FVec C A 1
a ⟩ = a ▻' FNil

mutual
  take : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} {A : Set ℓ₂} → (n : ℕ) → FStream C A → FVec C A n
  take ℕ.zero as = FNil
  take (ℕ.suc n) as = FCons (fmap (take' n) (inF as))

  take' : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} {A : Set ℓ₂} → (n : ℕ) → FStream' C A → A × FVec C A n
  proj₁ (take' n as) = head as
  proj₂ (take' n as) = take n (tail as)


⟨_▻⋯ : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁} {A : Set ℓ₂} {n : ℕ}
     → FVec C A (suc n) → FStream {i} C A
⟨ as ▻⋯ = aux as FNil
  where
    mutual
      aux : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁} {A : Set ℓ₂} {n m : ℕ}
           → FVec C A (suc n) → FVec C A m → FStream {i} C A
      inF (aux (FCons x) FNil) = fmap (aux2 (FCons x)) x
      inF (aux keep (FCons x)) = fmap (aux2 keep) x
      aux2 : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁} {A : Set ℓ₂} {n m : ℕ}
        → FVec C A (suc n) → A × FVec C A m → FStream' {i} C A
      head (aux2 keep (a , _)) = a
      tail (aux2 keep (_ , v)) = aux keep v

{-
Stuff that doesn't obviously work:
* drop, _at_ (Since side effects would have to be thrown away)
* _▸⋯  (Only if the given value is effectful or the functor is pointed, i.e. has a null effect (like Applicative or Monad))
-}

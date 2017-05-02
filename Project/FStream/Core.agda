module FStream.Core where

open import ContainerMonkeyPatched renaming (map to fmap) public
open import Data.Nat hiding (_⊔_)
open import Data.Product hiding (map)
open import Data.Vec using ([]; _∷_; Vec)
open import Level hiding (suc) renaming (zero to ℓ₀) public
open import Size public

mutual
  record FStream {i : Size} {ℓ₁ ℓ₂} (C : Container ℓ₁) (A : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
    -- random name
    --constructor F_
    inductive
    field
      inF : ⟦ C ⟧ (FStream' {i} C A)
  record FStream' {i : Size} {ℓ₁ ℓ₂} (C : Container ℓ₁) (A : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
    -- semirandom name
    constructor _▸_
    coinductive
    field
      head : A
      tail : {j : Size< i} → FStream {j} C A
open FStream public
open FStream' public

-- TODO Not a good idea to have two similar looking triangles
_►_ : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} {A : Set ℓ₂} → ⟦ C ⟧ A → FStream C A → FStream C A
inF (a ► as) = fmap (λ x → record { head = x ; tail = as }) a
-- f ► record { inF = inf } = record { inF = fmap ((λ z → head z ▸ tail z)) inf } -- Sebastian's solution

mutual
  -- Caution, this one pushes the side effects down one tick
  _►'_ : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁} {A : Set ℓ₂} → A → FStream {i} C A → FStream {i} C A
  inF (a ►' as) = fmap (helper a) (inF as)
  helper : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁} {A : Set ℓ₂} → A → FStream' {i} C A → FStream' {i} C A
  head (helper a as) = a
  tail (helper a as) = head as ►' tail as
  -- (λ x → record { head = a ; tail = head x ►' tail x })

{-
_►⋯' : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁} {A : Set ℓ₂} → A → FStream {i} C A
a ►⋯' = a ►' (a ►⋯')
-}
-- TODO Write the above without the direct recursion




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

repeat : {A : Set} → {C : Container ℓ₀} → ⟦ C ⟧ A -> FStream C A
proj₁ (inF (repeat (proj₁ , proj₂))) = proj₁
head (proj₂ (inF (repeat (proj₁ , proj₂))) x) = proj₂ x
tail (proj₂ (inF (repeat (proj₁ , proj₂))) x) = repeat (proj₁ , proj₂)

mutual
  corec : ∀ {i ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁} {A : Set ℓ₂} {X : Set ℓ₃} → (X → A × ⟦ C ⟧ X) → ⟦ C ⟧ X → FStream {i} C A
  inF (corec f x) = fmap (corec' f) x

  corec' : ∀ {i ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁} {A : Set ℓ₂} {X : Set ℓ₃} → (X → A × ⟦ C ⟧ X) → X → FStream' {i} C A
  head (corec' f x) = proj₁ (f x)
  tail (corec' f x) = corec f (proj₂ (f x))

infixr 5 _▻_
infix 6 ⟨_▻⋯
infix 7 _⟩

data FVec {ℓ₁ ℓ₂} (C : Container ℓ₁) (A : Set ℓ₂) : (n : ℕ) → Set (ℓ₁ ⊔ ℓ₂) where
  FNil : FVec C A 0
  FCons : ∀ {n} → ⟦ C ⟧ (A × FVec C A n) → FVec C A (suc n)

-- TODO Syntactic sugar for these as well
data FVec' {ℓ₁ ℓ₂} (C : Container ℓ₁) (A : Set ℓ₂) : (n : ℕ) → Set (ℓ₁ ⊔ ℓ₂) where
  FNil' : FVec' C A 0
  FCons' : ∀ {n} → A → ⟦ C ⟧ (FVec' C A n) → FVec' C A (suc n)

_▻'_ : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} {A : Set ℓ₂} {n} → A → ⟦ C ⟧ (FVec' C A n) → FVec' C A (suc n)
_▻'_ = FCons'


fVec'ToFVec : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} {A : Set ℓ₂} {n} → FVec' C A n → FVec C A n
fVec'ToFVec FNil' = FNil
fVec'ToFVec (FCons' a v) = FCons (fmap (λ x → a , fVec'ToFVec x) v)


nest : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} {A : Set ℓ₂} {n} → Vec (⟦ C ⟧ A) n → FVec C A n
nest [] = FNil
nest (a ∷ as) = FCons (fmap (_, nest as) a)


_▻_ :  ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} {A : Set ℓ₂} {n} → ⟦ C ⟧ A → (FVec C A n) → FVec C A (suc n)
a ▻ v = FCons (fmap (λ x → x , v) a)

_⟩ : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} {A : Set ℓ₂} → ⟦ C ⟧ A → FVec C A 1
a ⟩ = a ▻ FNil

mutual
  vmap : ∀ {ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁} {A : Set ℓ₂} {B : Set ℓ₃} {n} → (f : A → B) → FVec C A n → FVec C B n
  vmap _ FNil = FNil
  vmap f (FCons x) = FCons (fmap (vmap' f) x)

  vmap' : ∀ {ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁} {A : Set ℓ₂} {B : Set ℓ₃} {n} → (f : A → B) → A × FVec C A n → B × FVec C B n
  vmap' f (a , v) = f a , vmap f v

mutual
  take : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} {A : Set ℓ₂} → (n : ℕ) → FStream C A → FVec C A n
  take ℕ.zero as = FNil
  take (ℕ.suc n) as = FCons (fmap (take' n) (inF as))

  take' : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} {A : Set ℓ₂} → (n : ℕ) → FStream' C A → A × FVec C A n
  proj₁ (take' n as) = head as
  proj₂ (take' n as) = take n (tail as)

take'' : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} {A : Set ℓ₂} → (n : ℕ) → FStream' C A → FVec' C A n
take'' zero as = FNil'
take'' (suc n) as = FCons' (head as) (fmap (take'' n) (inF (tail as)))

_pre⟨_▻⋯' : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁} {A : Set ℓ₂} {m n}
     → FVec' C A m → FVec' C A (suc n) → FStream' {i} C A
head (FNil' pre⟨ FCons' a _ ▻⋯') = a
inF (tail (FNil' pre⟨ FCons' a v ▻⋯')) = fmap (_pre⟨ (FCons' a v) ▻⋯') v
head (FCons' x _ pre⟨ v' ▻⋯') = x
inF (tail (FCons' _ v pre⟨ v' ▻⋯')) = fmap (_pre⟨ v' ▻⋯') v



⟨_▻⋯' : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁} {A : Set ℓ₂} {n : ℕ}
     → FVec' C A (suc n) → FStream' {i} C A
⟨ v ▻⋯' = FNil' pre⟨ v ▻⋯'


mutual
  _pre⟨_▻⋯ : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁} {A : Set ℓ₂} {m n}
       → FVec C A m → FVec C A (suc n) → FStream {i} C A
  inF (FCons x pre⟨ keep ▻⋯) = fmap (_aux keep) x
  inF (FNil pre⟨ FCons x ▻⋯) = fmap (_aux (FCons x)) x
  _aux_ : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁} {A : Set ℓ₂} {n m : ℕ}
    → A × FVec C A m → FVec C A (suc n) → FStream' {i} C A
  head ((a , _ ) aux v) = a
  tail ((_ , v') aux v) = v' pre⟨ v ▻⋯

⟨_▻⋯ : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁} {A : Set ℓ₂} {n : ℕ}
     → FVec C A (suc n) → FStream {i} C A
⟨ as ▻⋯ = FNil pre⟨ as ▻⋯



{-
Stuff that doesn't obviously work:
* drop, _at_ (Since side effects would have to be thrown away)
  (One could at most delay the side effects somehow?)
* _▸⋯  (Only if the given value is effectful or the functor is pointed, i.e. has a null effect (like Applicative or Monad), or by delaying the side effects)
-}

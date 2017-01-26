module FStream.Core where

open import Data.Container
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Fin hiding (_+_)
open import Data.Product hiding (map)
open import Data.Unit
open import Level

mutual
  record FStream {ℓ} (C : Container ℓ) (A : Set ℓ) : Set ℓ where
    inductive
    field
      inF : ⟦ C ⟧ (FStream' C A)
  record FStream' {ℓ} (C : Container ℓ) (A : Set ℓ) : Set ℓ where
    coinductive
    field
      head : A
      tail : FStream C A
open FStream
open FStream'


ListC : Container Level.zero
Shape    ListC   = ℕ
Position ListC n = Fin n

eineListe : ⟦ ListC ⟧ ℕ
proj₁ eineListe = 2
proj₂ eineListe Fin.zero = 23
proj₂ eineListe (Fin.suc Fin.zero) = 42
proj₂ eineListe (Fin.suc (Fin.suc ()))

StateC : ∀ {ℓ} → Set ℓ → Container ℓ
Shape (StateC S) = S -> S
Position (StateC S) _ = S

ReaderC : Set → Container Level.zero
Shape (ReaderC R) = ⊤
Position (ReaderC R) _ = R


runReader : {R A : Set} → ⟦ ReaderC R ⟧ A → R → A
runReader (proj₁ , proj₂) r = proj₂ r

read : ∀ {R} → ⟦ ReaderC R ⟧ R
proj₁ read = tt
proj₂ read x = x

record PosNat : Set where
  constructor _because_
  field
    n   : ℕ
    n>0 : n > 0

drei : PosNat
drei = 3 because s≤s z≤n

{-

readDouble : ⟦ ReaderC ℕ ⟧ ℕ
readDouble = map (_* 2) read

data even : ℕ → Set where
  even0 : even 0
  evenss : {n : ℕ} → even n → even (ℕ.suc (ℕ.suc n))

n*2lemma : {n : ℕ} → even n -> even (2 + n)
n*2lemma p = {!   !}

n*2iseven : (n : ℕ) → even (2 * n)
n*2iseven ℕ.zero = even0
n*2iseven (ℕ.suc n) = {! evenss  !}

alwaysEven : (n : ℕ) → even (runReader readDouble n)
alwaysEven = {!   !}
-}

readSuc : ⟦ ReaderC ℕ ⟧ ℕ
readSuc = map (ℕ.suc) read

alwaysPos : (n : ℕ) → runReader readSuc n > 0
alwaysPos n = s≤s z≤n

alwaysPosC : □ (_> 0) readSuc
alwaysPosC = λ p → s≤s z≤n

sometimes3 : ◇ (_≡ 3) readSuc
sometimes3 = ℕ.suc (ℕ.suc ℕ.zero) , refl

sometimes5 : ◇ (_≡ 5) readSuc
sometimes5 = ℕ.suc (ℕ.suc (ℕ.suc (ℕ.suc ℕ.zero))) , refl

repeat : {A : Set} → {C : Container Level.zero} → ⟦ C ⟧ A -> FStream C A
proj₁ (FStream.inF (repeat (proj₁ , proj₂))) = proj₁
FStream'.head (proj₂ (FStream.inF (repeat (proj₁ , proj₂))) x) = proj₂ x
FStream'.tail (proj₂ (FStream.inF (repeat ca)) x) = repeat ca

-- Formalisiere: "repeat readSuc gibt immer >0 aus"
record ■ {A : Set} {C : Container Level.zero} (pred : A → Set) (cas : FStream C A) : Set where
  coinductive
  field
    now■ : □ {Level.zero} {C} {A} pred (map head (inF cas))
    later■ : □ {Level.zero} {C} {FStream C A} (■ pred) (map tail (inF cas))


data ◆ {A : Set} {C : Container Level.zero} (pred : A → Set) (cas : FStream C A) : Set where
  now◆ : ◇ {Level.zero} {C} {A} pred (map head (inF cas)) → ◆ pred cas
  later◆ : ◇ {Level.zero} {C} {FStream C A} (◆ pred) (map tail (inF cas)) → ◆ pred cas

always>0 : ■ (_> 0) (repeat readSuc)
■.now■ always>0 p = s≤s z≤n
■.later■ always>0 p = always>0

sumFrom : ℕ → FStream (ReaderC ℕ) ℕ
proj₁ (inF (sumFrom n0)) = tt
head (proj₂ (inF (sumFrom n0)) n) = n0 + n
tail (proj₂ (inF (sumFrom n0)) n) = sumFrom (n0 + n)

sum : FStream (ReaderC ℕ) ℕ
sum = sumFrom 0

eventuallysometimes>2 : ◆ (_> 2) sum
eventuallysometimes>2 = now◆ (ℕ.suc (ℕ.suc (ℕ.suc ℕ.zero)) , s≤s (s≤s (s≤s z≤n)))

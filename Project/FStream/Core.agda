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

-- ■ und ◆ stehen für die temporalen Modalitäten, A und E stehen für die Seiteneffekt-Modalitäten

record ■A {A : Set} {C : Container Level.zero} (pred : A → Set) (cas : FStream C A) : Set where
  -- Zu jeder Zeit, bei jedem Seiteneffekt ist pred erfüllt
  coinductive
  field
    nowA : □ {Level.zero} {C} {A} pred (map head (inF cas))
    laterA : □ {Level.zero} {C} {FStream C A} (■A pred) (map tail (inF cas))
open ■A

data ◆E {A : Set} {C : Container Level.zero} (pred : A → Set) (cas : FStream C A) : Set where
  -- Irgendwann könnte ein Seiteneffekt auftreten, sodass pred erfüllt ist
  alreadyE : ◇ {Level.zero} {C} {A} pred (map head (inF cas)) → ◆E pred cas
  notYetE : ◇ {Level.zero} {C} {FStream C A} (◆E pred) (map tail (inF cas)) → ◆E pred cas
open ◆E

-- Jederzeit ist die Ausgabe von repeat readSuc positiv, egal welche Werte reinkommen
always>0 : ■A (_> 0) (repeat readSuc)
nowA always>0 p = s≤s z≤n
laterA always>0 p = always>0

-- Summiert alle Werte in der Reader-Umgebung auf
sumFrom : ℕ → FStream (ReaderC ℕ) ℕ
proj₁ (inF (sumFrom n0)) = tt
head (proj₂ (inF (sumFrom n0)) n) = n0 + n
tail (proj₂ (inF (sumFrom n0)) n) = sumFrom (n0 + n)

sum : FStream (ReaderC ℕ) ℕ
sum = sumFrom 0

-- Es ist möglich, dass irgendwann die Summe größer als 2 ist
eventuallysometimes>2 : ◆E (_> 2) sum
eventuallysometimes>2 = alreadyE (ℕ.suc (ℕ.suc (ℕ.suc ℕ.zero)) , s≤s (s≤s (s≤s z≤n)))
-- und zwar schon nach dem ersten Schritt, falls 3 als Eingabe kommt


record ■E {A : Set} {C : Container Level.zero} (pred : A → Set) (cas : FStream C A) : Set where
  -- Jederzeit könnte ein Seiteneffekt auftreten, sodass pred erfüllt ist
  coinductive
  field
    nowE : ◇ {Level.zero} {C} {A} pred (map head (inF cas))
    laterE : ◇ {Level.zero} {C} {FStream C A} (■E pred) (map tail (inF cas))
open ■E


data ◆A {A : Set} {C : Container Level.zero} (pred : A → Set) (cas : FStream C A) : Set where
  -- Irgendwann ist ein Zeitpunkt erreicht, sodass unter jedem Seiteneffekt pred erfüllt wird
  alreadyA : □ {Level.zero} {C} {A} pred (map head (inF cas)) → ◆A pred cas
  notYetA : □ {Level.zero} {C} {FStream C A} (◆A pred) (map tail (inF cas)) → ◆A pred cas
open ◆A

-- Es ist jederzeit möglich, dass die Summe 2 übersteigt
alwaysSomehow>2 : ■E (_> 2) sum
nowE alwaysSomehow>2 = (ℕ.suc (ℕ.suc (ℕ.suc ℕ.zero)) , s≤s (s≤s (s≤s z≤n)))
laterE alwaysSomehow>2 = ℕ.zero , alwaysSomehow>2

module FStream.ModalityExamples where

open import ContainerMonkeyPatched renaming (map to fmap)
open import Data.Nat
open import FStream.Containers
open import FStream.Core
open import FStream.Modalities hiding (map)
open import Relation.Binary.PropositionalEquality
open import Data.Unit

readDouble : ⟦ ReaderC ℕ ⟧ ℕ
readDouble = fmap (_* 2) read


readSuc : ⟦ ReaderC ℕ ⟧ ℕ
readSuc = fmap (ℕ.suc) read

alwaysPos : (n : ℕ) → runReader readSuc n > 0
alwaysPos n = s≤s z≤n

alwaysPosC : □ (_> 0) readSuc
alwaysPosC = λ p → s≤s z≤n

sometimes3 : ◇ (_≡ 3) readSuc
sometimes3 = ℕ.suc (ℕ.suc ℕ.zero) , refl

sometimes5 : ◇ (_≡ 5) readSuc
sometimes5 = ℕ.suc (ℕ.suc (ℕ.suc (ℕ.suc ℕ.zero))) , refl


-- Jederzeit ist die Ausgabe von constantly readSuc positiv, egal welche Werte reinkommen
always>0 : GA (map (_> 0) (constantly readSuc))
nowA always>0 = λ p → s≤s z≤n
laterA always>0 = λ p → always>0

{-
nowA always>0 p = s≤s z≤n
laterA always>0 p = always>0
-}
-- Summiert alle Werte in der Reader-Umgebung auf
sumFrom : ℕ → FStream (ReaderC ℕ) ℕ
proj₁ (inF (sumFrom n0)) = tt
head (proj₂ (inF (sumFrom n0)) n) = n0 + n
tail (proj₂ (inF (sumFrom n0)) n) = sumFrom (n0 + n)

sum : FStream (ReaderC ℕ) ℕ
sum = sumFrom 0

-- Es ist möglich, dass irgendwann die Summe größer als 2 ist
eventuallysometimes>2 : FE (map (_> 2) sum)
eventuallysometimes>2 = alreadyE (ℕ.suc (ℕ.suc (ℕ.suc ℕ.zero)) , s≤s (s≤s (s≤s z≤n)))
-- und zwar schon nach dem ersten Schritt, falls 3 als Eingabe kommt


-- Es ist jederzeit möglich, dass die Summe 2 übersteigt
alwaysSomehow>2 : GE (map (_> 2) sum)
nowE alwaysSomehow>2 = ℕ.suc (ℕ.suc (ℕ.suc ℕ.zero)) , s≤s (s≤s (s≤s z≤n))
laterE alwaysSomehow>2 = ℕ.zero , alwaysSomehow>2
{-
nowE alwaysSomehow>2 = (ℕ.suc (ℕ.suc (ℕ.suc ℕ.zero)) , s≤s (s≤s (s≤s z≤n)))
laterE alwaysSomehow>2 = ℕ.zero , alwaysSomehow>2
-}

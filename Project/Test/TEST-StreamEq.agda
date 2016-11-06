module Test.TEST-StreamEq where

open import Stream.Stream
open import Stream.StreamEq
open import Size
open import Level
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Data.Nat renaming (suc to nSuc)
open import Function

n1 : Stream ℕ
n1 = corec (λ x → x , x + 1) 0

n2 : Stream ℕ
n2 = corec (λ x → x , x + 1) 0

n11 n22 : Stream ℕ
n11 = toStr nSuc
n22 = toStr nSuc

a1 a2 : Stream ℕ
hd a1 = 0
tl a1 = a1
hd a2 = 0
tl a2 = a2

a : Bisim (str-out' a1) (str-out' a2) 0 0
hdB a = refl
tlB a = a

b : Bisim ( (str-out' n11)) ( (str-out' n22)) 0 0
hdB b = refl
tlB b = b

c : Bisim ( (str-out' n1)) ( (str-out' n2)) 0 0
hdB c = refl
tlB c = c

--te : Bisim (λ x → x , x + 1) (λ x → x , x + 1) 0 0 → {!∃-Bisim!}
te : a1 ~ₛ a2
hd~ te = refl
tl~ te = te


tf : n1 ~ₛ n2
tf = ∃-Bisim gen1 gen2 init1 init2 {!!}
   where gen1 gen2 : ℕ → ℕ × ℕ
         init1 init2 : ℕ
         gen1 = {!strnout!}
         gen2 = {!!}
         init1 = {!!}
         init2 = {!!}

s1 : Stream ℕ
s1 = corec (λ x → x , (nSuc x)) 0

s2 : Stream ℕ
s2 = corec (λ x → x , (nSuc x)) 0

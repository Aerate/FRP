module Stream.Test.EX-Ampel where

open import Stream.Stream
open import Stream.RSet
open import Data.Bool
open import Data.Nat
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Product
open import Data.List
open import Relation.Nullary 
open import Data.Vec hiding (_⋎_) renaming (_∷_ to _▸_)

data TLight : Set where
  green : TLight
  red   : TLight

isRed : Stream TLight → RSet
isRed x = x ≡ₛ red ▸⋯  

stA1 stA2 : Stream TLight
stA1 = ⟨ green ▸ red ⟩ ▸⋯
stA2 = ⟨ red ▸ green ⟩ ▸⋯

--A1Red-U-A2Red : RSet
--A1Red-U-A2Red = (stA1 ≡ₛ red ▸⋯) U (stA2 ≡ₛ red ▸⋯)

pred2 : ⟦ (stA1 ≡ₛ red ▸⋯) U (stA2 ≡ₛ red ▸⋯) ⟧
now pred2 = finally refl
now (later pred2) = refl until (finally refl)
later (later pred2) = pred2

pred3 : ⟦ (stA1 ≡ₛ red ▸⋯) U (stA2 ≡ₛ red ▸⋯) ⟧ 
pred3 = {!!}

--  
liveness1 : ⟦ eventually (stA1 ≡ₛ green ▸⋯ ) ⟧
now liveness1 = ◇-now refl
now (later liveness1) = ◇-later (◇-now refl)
later (later liveness1) = liveness1

-- liveness1 mit ⟪_⟫ 

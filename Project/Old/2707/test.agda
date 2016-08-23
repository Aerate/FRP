open import Data.Empty
open import Data.Unit
open import Level
open import Data.Vec
open import Data.String

module test where

data test : Set where
  comb1 : ⊤ → ⊤ → test
  comb2 : ⊥ → ⊥ → test
  comb3 : ⊥ → ⊤ → test
  comb4 : ⊤ → ⊥ → test

data test2 : Set where
  comb1 : ⊤ → test2
  comb2 : ⊥ → test2

testf : (x : test) → test2
testf (comb1 x y) = comb1 tt
testf (comb2 x y) = comb1 tt
testf (comb3 x y) = comb1 tt
testf (comb4 x y) = comb2 y

testInst : test
testInst = comb1 tt tt

absurdUnit : ∀ {ℓ : Level}{A : Set ℓ} -> ⊤ -> A
absurdUnit {_} {A} tt = {!!}  

absurdEmpty : ∀ {A : Set} -> ⊥ -> A
absurdEmpty ()  

m : String
m = "Mira"

v : Vec String 1
v = m ∷ []

v2 : Vec String 0
v2 = []

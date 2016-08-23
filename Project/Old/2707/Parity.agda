open import Data.Nat

module Parity where


data Nat⁺ : Set where
  one : Nat⁺
  double : Nat⁺ → Nat⁺
  double+1 : Nat⁺ → Nat⁺

data Nat₂ : Set where
  zero : Nat₂
  id : Nat⁺ → Nat₂

data Parity : ℕ -> Set where
  even : (k : ℕ) -> Parity (k * 2)
  odd  : (k : ℕ) -> Parity (1 + k * 2)

parity : (n : ℕ) -> Parity n
parity zero = even zero
parity (suc n) with parity n
parity (suc .(k * 2)) | even k = odd k
parity (suc .(1 + k * 2)) | odd k = even (suc k)

data Par : Set where
  even : Par
  odd  : Par


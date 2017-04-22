
eineListe : ⟦ ListC ⟧ ℕ
proj₁ eineListe = 2
proj₂ eineListe Fin.zero = 23
proj₂ eineListe (Fin.suc Fin.zero) = 42
proj₂ eineListe (Fin.suc (Fin.suc ()))


record PosNat : Set where
  constructor _because_
  field
    n   : ℕ
    n>0 : n > 0

drei : PosNat
drei = 3 because s≤s z≤n

{-
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

data Parity : ℕ → Set where
  even : (k : ℕ) → Parity (k * 2)
  odd  : (k : ℕ) → Parity (1 + (k * 2))

parity : (n : ℕ) → Parity n
parity zero = even 0
parity (suc n) with parity n
parity (suc .(k * 2)) | even k = odd k
parity (suc .(1 + k * 2)) | odd k = even (ℕ.suc k)

*2l : ∀ {n} → Parity n → Parity (n * 2)
*2l (even k) = even (k * 2)
*2l (odd k)  = even (1 + (k * 2))

alwaysEven : (n : ℕ) → Parity (runReader readDouble n)
alwaysEven zero = even 0
alwaysEven (suc n) = even (1 + n)

alwaysEvenC : □ Parity readDouble
alwaysEvenC zero = even 0
alwaysEvenC (suc p) = even (1 + p)

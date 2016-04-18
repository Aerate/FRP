data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

infixl 60 _*_
infixl 40 _+_
infixr 20 _or_
infix 5 if_then_else_

--if_then_else_ : ∀ { a } → Bool → a → a → a 

_+_ : ℕ → ℕ → ℕ
zero + zero = zero
zero + n = n
(succ n) + m = succ (n + m)

_*_ : ℕ → ℕ → ℕ
zero   * m = zero
succ n * m = m + (n * m)

data _even : ℕ → Set where
  ZERO : zero even
  STEP : ∀ x → x even → succ (succ x) even

--pr₁ : succ ( succ (succ (succ (succ (succ zero))))) even
--pr₁ = STEP (succ (succ zero)) (STEP zero ZERO)
--pr₁ = STEP {!!} {!!}

data 𝔹 : Set where
  true  : 𝔹
  false : 𝔹

not : 𝔹 → 𝔹
not  true = false
not false = true

_or_ : 𝔹 → 𝔹 → 𝔹 
false or x = x
true or _ = true

if_then_else_ : {A : Set } → 𝔹 → A → A → A
if true then x else y = x
if false then x else y = y

infixr 40 _::_
data List (A : Set) : Set where
  [] : List A
  _::_ : A → List A → List A

infixr 40 _◀_
data _⋆ (α : Set) : Set where
  ε : α ⋆
  _◀_ : α → α ⋆ → α ⋆

ident : (A : Set) → A → A
ident A x = x

z' : ℕ
z' = ident ℕ zero

natrec : {C : Set} → C → (ℕ → C → C) → ℕ → C
natrec base stepf zero = base
natrec base stepf (succ args) = stepf args (natrec base stepf args)

plus : ℕ → ℕ → ℕ
plus m n = natrec m (λ x y →  succ y) n

x : ℕ
x = succ (succ zero)

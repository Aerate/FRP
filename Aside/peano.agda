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

natind : {P : ℕ → Set} → P zero → ((n : ℕ) → P n → P (succ n)) → (k : ℕ) → P k
natind base stepF zero = base
natind base stepF (succ n) = stepF n (natind base stepF n)

plus : ℕ → ℕ → ℕ
plus m n = natrec m (λ x y →  succ y) n

x : ℕ
x = succ (succ zero)

data Vec (A : Set) : ℕ → Set where
  nil  : Vec A zero
  _cons_ : {n : ℕ} → A → Vec A n → Vec A (succ n)

liste : Vec 𝔹 (succ zero)
liste = true cons nil

liste' : List 𝔹
liste' = true :: []

head : {A : Set} → List A → A
head [] = {!!}
head (a :: as) = a

repeat : {A : Set} → A → ℕ → List A
repeat a zero = []
repeat a (succ n) = a :: repeat a n

repeatVec : {A : Set} → A → (n : ℕ) → Vec A n
repeatVec a zero = nil
repeatVec a (succ n) = a cons repeatVec a n

head' : {A : Set} → {n : ℕ} → Vec A (succ n) → A
head' (a cons as) = a

bla : 𝔹
bla = head' liste


data _==_ {A : Set} : A → A → Set where
  refl : {x : A}  → x == x


app : {A , B : Set}{x , y : A}{f : A → B} → x == y → f x == f y
app refl = refl


compVec : {A : Set} → {n : ℕ} → {v1 , v2 : Vec A n} → v1 == v2 → {a1 , a2 : A} → a1 == a2 → (a1 cons v1) == (a2 cons v2)
compVec refl refl = refl


0g0 : zero == zero
0g0 = refl

nats : (n : ℕ) → Vec ℕ (succ n)
nats = ?

map : {A , B : Set} → (f : A → B) → {n : ℕ} → Vec A n → Vec B n
map = ?

tail : {A : Set}{n : ℕ} → Vec A (succ n) → Vec A n
tail = ?

posnats : {n : ℕ} → tail (nats (succ n)) == map succ (nats n)
posnats = ?

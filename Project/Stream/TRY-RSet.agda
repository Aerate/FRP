module Stream.TRY-RSet where

open import Stream.RSet
open import Stream.Stream
open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Empty

tt : Stream Bool
hd tt = true
tl tt = tt

ff : Stream Bool
hd ff = false
tl ff = ff

st0 : Stream Set
hd st0 = Bool
tl st0 = st0

st1 : Stream Set
st1 = ⟪ Bool ⟫

triv : Set
triv = true ≡ true

triv2 : Set
triv2 = true ≡ false

ax1 : true ≡ false → ⊥
ax1 ()

ax2 : false ≡ true → ⊥
ax2 ()

st2 : Stream Set
st2 = ⟪ triv ⟫

st3 : Stream Set
st3 = ⟪ triv ⟫

fun : Set → Bool
fun x = {!!}

eqq : (s1 : Stream Set) → s1 ≡ s1
eqq s1 = refl

data _eq_ (S T : Stream Set) : Set₁ where
  ref : S ≡ T →  S eq T

data _seq_ {A : Set} (S T : Stream A) : Set where
  srefl : (hd S) ≡ (hd T) → S seq T
  snot  : (¬ (hd S) ≡ (hd T)) → S seq T

dif1 dif2 : Stream Bool
hd dif1 = false
tl dif1 = tt
hd dif2 = false
tl dif2 = ff

try5 : dif1 seq dif2
try5 = srefl refl

try6 : dif1 seq tt
try6 = snot (λ x → (ax2 x))

try2 : st2 eq st2
try2 = ref refl

try3 : st2 eq st1
try3 = ref {!!}

st4 : Stream Set
hd st4 = triv
tl st4 = st4

try : RSet
try = st3

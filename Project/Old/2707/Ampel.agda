module Ampel where

open import NewStream
open import Data.Nat
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Product
open import Data.List
open import Size

data Ampel : Set where
  gruen : Ampel
  rot   : Ampel

G R : Ampel
G = gruen
R = rot

switch : Ampel → Ampel
switch gruen = rot
switch rot = gruen

switchₛ : Stream Ampel → Stream Ampel
switchₛ = lift1-1 switch
swS = switchₛ

next : Stream Ampel → Stream Ampel
next s = λ x → swS s (x + 1)

sequenceR : Stream Ampel → Stream Ampel
sequenceR t s = t (s + 2)

a1 a2 : Stream Ampel
a1 = λ x → gruen
a2 = λ x → rot

--_▹_ : ∀ {i : Size} {j : Size< i} -> Ampel -> Stream {i} Ampel -> Stream {j} Ampel
--(a ▹ s) zero = a
--(a ▹ s) (suc n) = s n

--_▹_ : Ampel -> Stream Ampel -> Stream Ampel
--(a ▹ s) zero = a
--(a ▹ s) (suc n) = s n

an0 : Stream Ampel
an0 = swS a1

-- howTo: t1 depend on t0! 
record streamAmpel {i : Size} Ampel : Set where
  coinductive
  constructor _►_
  field
    init : Ampel  
    nxt  : ∀ {j : Size< i} → streamAmpel {j} Ampel
open streamAmpel



am : Stream Ampel
am 0 = rot
am (suc n) = switch (am n)

--am0 am1 : generalStream Ampel
--am0 = gruen ▸ (am1)
--am1 = rot ▸ (♭ am0)

-- {-# TERMINATING #-}
-- am0 am1 am3 : Stream Ampel
-- am0 = gruen ▹ am3
-- am1 = gruen ▹ (λ x → rot)
-- am3 = rot ▹ am0

-- am2 : Ampel → Stream Ampel
-- am2 a = a ▹ (λ x → switch a)

-- prop : RSet
-- prop = a2 ≡ₛ const gruen

-- proof : ⟦ ¬ₛ prop ⟧
-- proof ()

-- prop2 : RSet
-- prop2 = ¬ₛ ((a2 ≡ₛ const gruen) ×ₛ (a1 ≡ₛ const gruen))

-- lem1 : rot ≡ gruen → ⊥
-- lem1 ()

-- proof2 : ⟦ prop2 ⟧
-- proof2 = λ x → lem1 (proj₁ x)


 


-- -- --Todo
-- {-

-- -- a1 : gerade Zeiten gruen
-- -- a2 : ungerade zeiten gruen
-- -- ------------------------
-- -- (Beweis prop1 wird nicht klappen, aber prop2)
-- -- (Beweis fuer prop2: case)
-- -- ------------------------
-- -- - Diamond & Box to RSet
-- -- -----------------------
-- -- jede ampel wird mal wieder gruen (diamond gruen)


-- switch : RSet → RSet
-- switch s = ¬ₛ s 

-- -}

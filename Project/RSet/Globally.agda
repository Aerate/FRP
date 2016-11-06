module RSet.Globally where

open import RSet.Core
open import RSet.Next


record hd□ (R : RSet) : Set where
  inductive
  field
    □-now   : hd R
    □-later : hd□ (○ R)

□ : ∀ {i : Size} → RSet → RSet
hd (□ x) = hd□ x
tl (□ x) = □ (tl x)

--□ : ∀ {i : Size} → RSet → RSet
--hd (□ x) = ⟦ x ⟧
--tl (□ x) = □ (tl x)

--□ : ∀ {i : Size} → RSet → RSet
--hd (□ A) = hd A
--tl (□ A) = □ (tl A)

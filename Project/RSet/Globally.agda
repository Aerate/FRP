module RSet.Globally where

open import RSet.Core
open import RSet.Next

{-
For □ to be satisfiable over some RSet φ, 
φ needs to have a witness now as well as  
later.
-}

record □ (φ : RSet) : Set where
  coinductive
  field
    □-now   : hd φ
    □-later : □ (○ φ)
open □ public

□ₛ : ∀ {i : Size} → RSet → RSet
hd (□ₛ x) = □ x
tl (□ₛ x) = □ₛ (tl x)
always = □ₛ

-- a synonym for negating
never : ∀ {i : Size} → RSet → RSet
never = ¬ₛ_

open import RSet.Core 

module RSet.Next where

{-
For ○ to be satisfiable over some RSet φ, 
φ must have a witness at the next element.
-}

data ○ₛ_ (φ : RSet) : Set where
  next : (hd (tl φ)) → ○ₛ φ

○ : ∀ {i : Size} → RSet → RSet
○ A = tl A


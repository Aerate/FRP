open import RSet.Core 

module RSet.Next where

○ : ∀ {i : Size} → RSet → RSet
○ A = tl A


module RSet.Examples.Crossing.EX-Safety where

open import RSet
open import RSet.Core
open import RSet.Properties.Reasoning
open import RSet.Examples.Crossing.TrafficLight 


{-
-----------------
-- Safety
-----------------  

Arbitrary requirement:
Two transitions (t₀, t₁) of lights are safe iff they are in different states (s₀ s₁) for all time except when they are both yellow, i.e.

Safe = {(s₀, s₁) | s₀ ≢ s₁ ∨ (s₀ s₁ ≡ yellow)}.

As LTL-formula this can be expressed by □ (green(t₀) ⇒ ¬ ○ red(t₁))
-}

transition₀ = ⟨ yellow ▸ green ▸ yellow ▸ red ⟩ ▸⋯ 
transition₁ = ⟨ yellow ▸ red ▸ yellow ▸ green ⟩ ▸⋯

safety = □ (is green transition₀ ⇒ ¬ₛ (○ (is red transition₁)))

{-
Obviously this holds for the given example. Lets check the property nonetheless:
To always hold it is necessary for the RSet of proofs to be 'empty' in the sense that
we could not construct any witness for the opposite, now or ever:
-}

proof-safety : safety                                               
□-now proof-safety () t₁                                            -- (0) : t₀ → ⊥ since t₀ is yellow ; t₁ not relevant
□-now (□-later proof-safety) refl ()                                -- (1) : t₀ → refl since 't₀ is green' holds, implying 'next t₁ is red' to be t₁ → ⊥ 
□-now (□-later (□-later proof-safety)) () t₁                        -- (2) : t₀ → ⊥ since t₀ is yellow; t₁ not relevant
□-now (□-later (□-later (□-later proof-safety))) () t₁              -- (3) : t₀ → ⊥ since t₀ is red; t₁ not relevant
□-later (□-later (□-later (□-later proof-safety))) = proof-safety   -- (4) : recursive call

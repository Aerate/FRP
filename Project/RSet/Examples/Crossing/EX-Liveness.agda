module RSet.Examples.Crossing.EX-Liveness where

open import RSet
open import RSet.Core
open import RSet.Properties.Reasoning
open import RSet.Examples.Crossing.TrafficLight 

{-
-----------------
-- Liveness
-----------------  

A simple liveness:
If a traffic light is red it eventually shall become green at some future time and vice versa.

As LTL-formula this can be expressed by □ ((green ⇒ ◇ red) ∧ (red ⇒ ◇ green))
-}

states₀ =  ⟨ green ▸ green ▸ yellow ▸ red ▸ red ▸ yellow ⟩ ▸⋯

liveness₀ = □ (is green states₀ ⇒ (◇ (is red states₀)))

proof-live₀ : liveness₀
□-now proof-live₀ x = ◇-later (◇-later (◇-later (◇-now refl)))
□-now (□-later proof-live₀) x = ◇-later (◇-later (◇-now refl))
□-now (□-later (□-later proof-live₀)) x = ◇-later (◇-now refl)
□-now (□-later (□-later (□-later proof-live₀))) x = ◇-now refl
□-now (□-later (□-later (□-later (□-later proof-live₀)))) ()
□-now (□-later (□-later (□-later (□-later (□-later proof-live₀))))) ()
□-later (□-later (□-later (□-later (□-later (□-later proof-live₀))))) = proof-live₀

liveness₁ = □ (is red states₀ ⇒ (◇ (is green states₀)))

proof-live₁ : liveness₁
□-now proof-live₁ ()
□-now (□-later proof-live₁) ()
□-now (□-later (□-later proof-live₁)) ()
□-now (□-later (□-later (□-later proof-live₁))) refl =  ◇-later (◇-later (◇-later (◇-now refl)))
□-now (□-later (□-later (□-later (□-later proof-live₁)))) x = ◇-later (◇-later (◇-now refl))
□-now (□-later (□-later (□-later (□-later (□-later proof-live₁))))) x =  ◇-later (◇-now refl)
□-later (□-later (□-later (□-later (□-later (□-later proof-live₁))))) = proof-live₁

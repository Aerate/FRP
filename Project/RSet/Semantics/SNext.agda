module RSet.Semantics.SNext where

open import RSet.Semantics.Rules
open import RSet.Core
open import RSet.Next

-- --semi-haendische reduktion zu NF :
-- hd (tl (c (λ x → mapₛ embed (b x)))) !≡! hd (c (λ x → mapₛ embed (tl (b x))))
--
-- c auch lesbar als {c : (B → Stream Set) → Stream Set} ?
-- 
-- _≈_.f = hd (tl ( { ?? } (op ○ c (lift1 embed ∘ b)) ))
sem-○ : ∀ {B : Set} (b : B → Stream Bool) (c : cont B) → ((drop1 b) ⊨ c) ≈ (b ⊨ (op ○ c))
_≈_.f (sem-○ b c) x = hd (tl ( lift1 {!!} (op ○ c (lift1 embed ∘ b)) ))
_≈_.g (sem-○ b c) x = {!!}
_≈_.invₗ (sem-○ b c) = {!!}
_≈_.invᵣ (sem-○ b c) = {!!}


module RSet.Examples.EX-Future where

open import Data.Nat
open import Data.Bool
open import Data.Product hiding (map)
open import Function

open import RSet.Core
open import RSet.Next
open import RSet.Future
open import RSet.Properties.Reasoning

-- get the stream of natural numbers 

Nats : Stream ℕ
Nats = corec (λ x → x , (suc x)) 0

-- form a predicate over this stream, for example, the relation less-than-or-equal 
-- proposition: (3 ≤_) will be eventually valid over Nats. 

check₁ : eval ◇ (map (3 ≤_ ) Nats)
validity check₁ = holds (◇-later (◇-later (◇-later (◇-now (s≤s (s≤s (s≤s z≤n)))))))

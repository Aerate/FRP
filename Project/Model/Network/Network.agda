module Network.Network where

open import Data.Nat hiding (_<_)
open import Data.Product as Prod
open import Data.Sum as Sum
open import Data.Fin hiding (_<_;_+_)
open import Data.Bool
open import Data.Unit
open import Data.Empty
open import Stream.Stream

open import Relation.Binary
open import Relation.Binary.PropositionalEquality

record Network : Set₁ where
 field
    Segment : Set
    Train : Set
    DecidableTrain : Decidable (_≡_ {A = Train})
    Route : Set
    DecidableRoute : Decidable (_≡_ {A = Route})
    RouteConnected : (s₁ s₂ : Route) → Set
    SegInRoute : Segment → Route → Set
    FacingInRoute : (s : Segment) → (rt : Route) → Set
    WellFormedRoutes : {ts : Segment} → ∀ rt₁ rt₂ rt₃ → RouteConnected rt₁ rt₂ → RouteConnected rt₃ rt₂
                       → Σ Segment (λ x → SegInRoute ts rt₁ × SegInRoute ts rt₃)

module RSet.Globally.Proof where

open import RSet.Globally
open import Stream.Stream
open import Stream.StreamUtils

open import Data.Nat
open import Data.Vec
open import Size

data □proof : {n : ℕ} → (props : Vec Set n) → Set where
  □nil : □proof []
  _□cons_ : ∀ {n} → {prop : Set} → {props : Vec Set n} → (proof : prop) → (proofs : □proof props) → □proof (prop ∷ props)
open □proof

-- TODO Find out how to write the following with sizes
{-# NON_TERMINATING #-}
_pre□cycle_ : ∀ {m n} → {props : Vec Set m} → {props' : Vec Set (suc n)} → □proof props → □proof props' → □ (props ∷⟨ props' ▸⋯)
□-now (□nil pre□cycle (proof □cons proofs)) = proof
□-later (□nil pre□cycle (proof □cons proofs)) = lemma (proofs pre□cycle (proof □cons proofs))
  where
    lemma : ∀ {n} → {prop : Set} → {props : Vec Set n} → □ (props ∷⟨ (prop ▸ props) ▸⋯) → □ (tl ([] ∷⟨ (prop ▸ props) ▸⋯))
    □-now (lemma x) = □-now x
    □-later (lemma x) = □-later (lemma x)
□-now ((proof □cons proofs) pre□cycle proofs') = proof
□-later ((proof □cons proofs) pre□cycle proofs') = proofs pre□cycle proofs'

□cycle : ∀ {n} → {props : Vec Set (suc n)} → □proof props → □ ⟨ props ▸⋯
□cycle proofs = □nil pre□cycle proofs

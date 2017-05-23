module RSet.Globally.Proof where

open import RSet.Core
open import RSet.Globally
open import Stream.Stream
open import Stream.StreamEq
open import Stream.StreamUtils

open import Data.Nat
open import Data.Vec renaming (map to vmap)
open import Relation.Binary.PropositionalEquality
open import Size

-- Consider renaming to □[] and □▸ or so
data □proof : {n : ℕ} → (props : Vec Set n) → Set where
  □nil : □proof []
  _□cons_ : ∀ {n} → {prop : Set} → {props : Vec Set n} → (proof : prop) → (proofs : □proof props) → □proof (prop ∷ props)
open □proof

-- TODO Probably need to put sizes in □ in order to make it terminate
{-# NON_TERMINATING #-}
_pre□cycle_ : ∀ {m n} → {props : Vec Set m} → {props' : Vec Set (suc n)} → □proof props → □proof props' → □ (props ∷⟨ props' ▸⋯)
□-now (□nil pre□cycle (proof □cons proofs)) = proof
□-later (□nil pre□cycle (proof □cons proofs)) = proofs pre□cycle (proof □cons proofs)
□-now ((proof □cons proofs) pre□cycle proofs') = proof
□-later ((proof □cons proofs) pre□cycle proofs') = proofs pre□cycle proofs'

□cycle : ∀ {n} → {props : Vec Set (suc n)} → □proof props → □ ⟨ props ▸⋯
□cycle proofs = □nil pre□cycle proofs

□repeat : {prop : Set} → prop → □ (prop ▸⋯)
□-now (□repeat proof) = proof
□-later (□repeat proof) = □repeat proof

-- TODO Rewrite for the □cycle ones
□map : ∀ {ℓ} {A : Set ℓ} {f : A → Set} {a : A} → f a → □ (map f (a ▸⋯))
□-now (□map proof) = proof
□-later (□map proof) = □map proof

□lift2 : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {f : A → B → Set} {a : A} {b : B} → f a b → □ (lift2 f (a ▸⋯) (b ▸⋯))
□-now (□lift2 proof) = proof
□-later (□lift2 proof) = □lift2 proof

mapLemma~ : ∀ {A : Set} {B : Set} {f : A → B} {a : A} → map f (a ▸⋯) ~ₛ (f a ▸⋯)
hd~ mapLemma~ = refl
tl~ mapLemma~ = mapLemma~

mapLemma : ∀ {A : Set} {B : Set} {f : A → B} {a : A} → □ (map f (a ▸⋯) ≡ₛ (f a ▸⋯))
mapLemma = ~ₛ→≡ₛ mapLemma~

-- TODO Maybe rather have these lemmas as bisimulations, since these are easier composable?
vmapLemma : ∀ {A : Set} {B : Set} {f : A → B} {m} {n} {v : Vec A m} {v' : Vec A (suc n)} → □ (map f (v ∷⟨ v' ▸⋯) ≡ₛ ((vmap f v) ∷⟨ (vmap f v') ▸⋯))
vmapLemma {v = v} {v' = v'} = vmapLemma' v v'
  where
    vmapLemma' : ∀ {A : Set} {B : Set} {f : A → B} {m} {n} (v : Vec A m) (v' : Vec A (suc n)) → □ (map f (v ∷⟨ v' ▸⋯) ≡ₛ ((vmap f v) ∷⟨ (vmap f v') ▸⋯))
    □-now (vmapLemma' [] (x ▸ v')) = refl
    □-later (vmapLemma' [] (x ▸ v')) = vmapLemma' v' (x ▸ v')
    □-now (vmapLemma' (x ▸ v) v') = refl
    □-later (vmapLemma' (x ▸ v) v') = vmapLemma' v v'







--

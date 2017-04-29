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
□prove : ∀ {n} → {props : Vec Set (suc n)} → □proof props → □ ⟨ props ▸⋯
□prove {n0} {props0} proofs0 = □aux props0 [] proofs0 □nil
  where
    lemma1 : ∀ {i : Size} {n} → (prop : Set) → (props : Vec Set n) → □ (props prefix ⟨ (prop ▸ props) ▸⋯) → □ (tl ([] prefix ⟨ prop ▸ props ▸⋯))
    □-now (lemma1 prop [] x) = □-now x
    □-now (lemma1 prop (prop' ▸ props) x) = □-now x
    □-later (lemma1 prop [] x) = □-later x
    □-later (lemma1 prop (prop' ▸ props) x) = □-later (lemma1 prop (prop' ▸ props) x)
    □aux : ∀ {n m} → (props : Vec Set (suc n)) → (props' : Vec Set m) → □proof props → □proof props' → □ (props' prefix ⟨ props ▸⋯)
    □-now (□aux (prop ∷ props) [] (proof □cons proofs) □nil) = proof
    □-later (□aux {n} {m} (prop ∷ props) [] (proof □cons proofs) □nil) = lemma1 prop props (□aux (prop ▸ props) props (proof □cons proofs) proofs)
    □-now (□aux props (x ∷ props') proofs (proof □cons proofs')) = proof
    □-later (□aux props (x ∷ props') proofs (proof □cons proofs')) = □aux props props' proofs proofs'















--

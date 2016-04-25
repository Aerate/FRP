module BooleanTheorems where

open import postulates
open import BooleanTypes

¬-Elim : ∀ (b : 𝔹) → ¬ (¬ b) ≡ b
¬-Elim tt = refl
¬-Elim ff = refl

∧-Elim : ∀ (b : 𝔹) → (b ∧ b) ≡ b
∧-Elim tt = refl
∧-Elim ff = refl 

⇒-Elim : ∀ (b : 𝔹) → (b ⇒ tt) ≡ tt
⇒-Elim tt = refl
⇒-Elim ff = refl

⇒-Elim2 : ∀ {b : 𝔹} → (tt ⇒ b) ≡ b
⇒-Elim2 {tt} = refl
⇒-Elim2 {ff} = refl

--ite-Elim : ∀ {b : 𝔹} {A B : Set} → (if tt then A else B) ≡ A
--ite-Elim 

ite-Elim : ∀ {b : 𝔹} {A B : Set} → (if b then A else A) ≡ A
ite-Elim {tt} = refl
ite-Elim {ff} = refl

ite-Elim2 : {A B : Set} → (if tt then A else B) ≡ A
ite-Elim2  = refl

ite-Elim3 : ∀ {b : 𝔹} {A B : Set} → (if ff then A else B) ≡ B
ite-Elim3 {tt} = refl
ite-Elim3 {ff} = refl


⇒-Elim3 : ∀ (b : 𝔹) → (ff  ⇒ b) ≡ tt
⇒-Elim3 ff  = refl
⇒-Elim3 tt = refl


⇒-Elim4 : ∀ (b : 𝔹) → (b  ⇒ tt) ≡ tt
⇒-Elim4 ff  = refl
⇒-Elim4 tt = refl

⇒-Elim5 : ∀ (b : 𝔹) → (b  ⇒ ff) ≡ ¬ b
⇒-Elim5 ff  = refl
⇒-Elim5 tt = refl

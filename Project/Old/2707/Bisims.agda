{-# OPTIONS --copatterns --sized-types #-}

open import Size
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P
open ≡-Reasoning

open import Data.List using (List; module List; []; _∷_; _++_; length)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; proj₁; proj₂)

-- Sized streams via head/tail.

record Stream {i : Size} (A : Set) : Set where
  coinductive
  constructor _∷_
  field
    hd : A
    tl : ∀ {j : Size< i} → Stream {j} A
open Stream public

-- Stream equality is bisimilarity
record _∼ˢ_ {A : Set} (s t : Stream A) : Set where
  coinductive
  field
    hd∼ : hd s ≡ hd t
    tl∼ : (tl s) ∼ˢ (tl t)
open _∼ˢ_ public

record Bisim {A X Y : Set}
  (c : X → A × X) (d : Y → A × Y) (x : X) (y : Y) : Set where
  coinductive
  field
    ins : proj₁ (c x) ≡ proj₁ (d y)
    con : Bisim c d (proj₂ (c x)) (proj₂ (d y))
open Bisim public


-- Functoriality.

map : ∀ {i A B} (f : A → B) (s : Stream {i} A) → Stream {i} B
hd (map     f s)     = f (hd s)
tl (map {i} f s) {j} = map {j} f (tl s {j})

-- (weak) Finality
corec : ∀ {A X : Set} → (X → A × X) → (∀ {i} → X → Stream {i} A)
hd (corec f x) = proj₁ (f x)
tl (corec f x) = corec f (proj₂ (f x))

-- Bisimulations

ext_proof : ∀{A X Y : Set} (c : X → A × X) (d : Y → A × Y) (x : X) (y : Y) → Bisim c d x y → (corec c x) ∼ˢ (corec d y)
hd∼ (ext_proof c d x y p) = ins p
tl∼ (ext_proof c d x y p) = ext_proof c d x' y' (con p)
  where
    x' = proj₂ (c x)
    y' = proj₂ (d y)

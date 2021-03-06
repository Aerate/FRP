module FStream.Proof where

open import Relation.Binary.PropositionalEquality

open import Library
open import FStream.Bisimulation
open import FStream.Core
open import FStream.FVec
open import FStream.Modalities

data proofAG' {ℓ₁ ℓ₂} {C : Container ℓ₁} : {n : ℕ} → (props : FVec' C (Set ℓ₂) n) → Set (ℓ₁ ⊔ ℓ₂) where
  []AG' : proofAG' FNil'
  _▻AG'_ : ∀ {prop : Set ℓ₂} {n} {props : ⟦ C ⟧ (FVec' C (Set ℓ₂) n)} → prop → A (fmap proofAG' props) → proofAG' (FCons' prop props)


_preCycleAG'_ : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁} {m n} {props : FVec' C (Set ℓ₂) m} {props' : FVec' C (Set ℓ₂) (suc n)} → proofAG' props → proofAG' props' → AG' {i} (props pre⟨ props' ▻⋯')
nowA' ([]AG' preCycleAG' (proof ▻AG' _)) = proof
laterA' ([]AG' preCycleAG' (proof ▻AG' proofs)) p = (proofs p) preCycleAG' (proof ▻AG' proofs)
nowA' ((proof ▻AG' _) preCycleAG' _) = proof
laterA' ((_ ▻AG' proofs) preCycleAG' proofs') p = (proofs p) preCycleAG' proofs'

cycleAG' : ∀ {i} {ℓ₁ ℓ₂} {C : Container ℓ₁} {n} {props : FVec' C (Set ℓ₂) (suc n)} → proofAG' props → AG' {i} (FNil' pre⟨ props ▻⋯')
cycleAG' proofs = []AG' preCycleAG' proofs

data proofAG {ℓ₁ ℓ₂} {C : Container ℓ₁} : {n : ℕ} → (props : FVec C (Set ℓ₂) n) → Set (ℓ₁ ⊔ ℓ₂) where
  []AG : proofAG FNil
  ConsAG : ∀ {n} {props : ⟦ C ⟧ (Set ℓ₂ × FVec C (Set ℓ₂) n)} → A (fmap (λ x → (proj₁ x) × (proofAG (proj₂ x))) props) → proofAG (FCons props)
  -- TODO This constructor type signature is an abomination and should be somehow rewritten with proofAG, but how??
  -- TODO props should be of type FVec C (Set ℓ₂) (suc n) maybe? Or is it easier this way?



{-
mapAG : ∀ {i} {ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁} {A : Set ℓ₂} {f : A → Set ℓ₃} {m n} → (v : FVec C A m) → (v' : FVec C A (suc n)) → AG {i} ((vmap f v pre⟨ vmap f v' ▻⋯)) → AG {i} (map f (v pre⟨ v' ▻⋯))
nowA' (mapAG FNil (FCons x) proofs p) = nowA' (proofs p)
nowA' (mapAG (FCons x) v proofs p) = nowA' (proofs p)
laterA' (mapAG FNil (FCons (shape , vals)) proofs p) p₁ with vals p
... | a , v = mapAG v (FCons (shape , vals)) (laterA' (subst (λ x → {!   !}) refl (proofs p))) p₁
-- laterA' (mapAG FNil v' proof p) p₁ = mapAG ({!   !}) (FCons {!   !}) (λ p₂ → laterA' (proof {!   !}) {!   !}) {!   !}
laterA' (mapAG (FCons x) v' proofs p) p₁ = {!   !}
-}

{-
mapAG : ∀ {i} {ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁} {A : Set (lsuc ℓ₃)} {f : A → Set ℓ₃} {m n} → {v : FVec C A m} → {v' : FVec C A (suc n)} → AG {i} ((vmap f v pre⟨ vmap f v' ▻⋯)) → AG {i} (map f (v pre⟨ v' ▻⋯))
nowA' (mapAG proof pos) = nowA' (proof pos)
laterA' (mapAG x p) = {!   !}
-}

_pre⟨_▻AG : ∀ {i} {ℓ₁ ℓ₂} {C : Container ℓ₁} {m n} {props : FVec C (Set ℓ₂) m} → {props' : FVec C (Set ℓ₂) (suc n)} → proofAG props → proofAG props' → AG {i} (props pre⟨ props' ▻⋯)
nowA' ( ([]AG pre⟨ (ConsAG proofs) ▻AG) p) = proj₁ (proofs p)
laterA' ( ([]AG pre⟨ (ConsAG proofs) ▻AG) p) p₁ = (proj₂ (proofs p) pre⟨ ConsAG proofs ▻AG) p₁
nowA' ( ((ConsAG proofs) pre⟨ _ ▻AG) p) = proj₁ (proofs p)
laterA' ( ((ConsAG proofs) pre⟨ proofs' ▻AG) p) p₁ = (proj₂ (proofs p) pre⟨ proofs' ▻AG) p₁
-- The p are the inputs (positions) from the side effects.

mapprecycle : ∀ {i} {ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁} {A : Set ℓ₂} {f : A → Set ℓ₃} {m n} (v : FVec C A m) → (v' : FVec C A (suc n)) → proofAG (vmap f v) → proofAG (vmap f v') → AG {i} (map f (v pre⟨ v' ▻⋯))
nowA' (mapprecycle FNil (FCons x) []AG (ConsAG proofs) p) with proofs p
...                                                          | proof , proofs' = proof
laterA' (mapprecycle FNil (FCons (shape , vals)) []AG (ConsAG proofs) p) p' with proofs p
... | proof , proofs' with vals p
...                    | a , v = mapprecycle v (FCons (shape , vals)) proofs' (ConsAG proofs) p'
nowA' (mapprecycle (FCons x) v' (ConsAG proofs) proofs' p) = proj₁ (proofs p)
laterA' (mapprecycle (FCons (shape , vals)) (FCons x) (ConsAG proofs) proofs' p) p₁ with proofs p
... | proof , proofs'' with vals p
...                       | a , v = mapprecycle v (FCons x) proofs'' proofs' p₁

⟨_▻AG : ∀ {i} {ℓ₁ ℓ₂} {C : Container ℓ₁} {n} {props : FVec C (Set ℓ₂) (suc n)} → proofAG props → AG {i} (FNil pre⟨ props ▻⋯)
⟨_▻AG = []AG pre⟨_▻AG

-- _⟩AG : ∀ {i} {ℓ₁ ℓ₂} {C : Container ℓ₁}

data proofEG {ℓ₁ ℓ₂} {C : Container ℓ₁} : {n : ℕ} → (props : FVec C (Set ℓ₂) n) → Set (ℓ₁ ⊔ ℓ₂) where
  []EG : proofEG FNil
  ConsEG : ∀ {n} {props : ⟦ C ⟧ (Set ℓ₂ × FVec C (Set ℓ₂) n)} → E (fmap (λ x → (proj₁ x) × (proofEG (proj₂ x))) props) → proofEG (FCons props)

_pre⟨_▻EG : ∀ {i} {ℓ₁ ℓ₂} {C : Container ℓ₁} {m n} {props : FVec C (Set ℓ₂) m} → {props' : FVec C (Set ℓ₂) (suc n)} → proofEG props → proofEG props' → EG {i} (props pre⟨ props' ▻⋯)
proj₁ ([]EG pre⟨ ConsEG (pos , _) ▻EG) = pos
nowE' (proj₂ ([]EG pre⟨ ConsEG (_ , proof , _) ▻EG)) = proof
laterE' (proj₂ ([]EG pre⟨ ConsEG (pos , proof , proofs) ▻EG)) = proofs pre⟨ ConsEG (pos , proof , proofs) ▻EG
proj₁ (ConsEG (pos , _) pre⟨ _ ▻EG) = pos
nowE'   (proj₂ (ConsEG (pos , proof , proofs) pre⟨ _ ▻EG)) = proof
laterE' (proj₂ (ConsEG (_   , _     , proofs) pre⟨ v ▻EG)) = proofs pre⟨ v ▻EG


-- TODO It's worth a thought whether we want to roll our own Sigma types
-- in order to have more meaningful projector names than projᵢ

infixr 5 _▻EG_
infix 6 ⟨_▻EG
infix 7 _⟩EG

infixr 5 _▻EG₁_
infix 7 _⟩EG₁

-- TODO Rename to ⟨_▻EG⋯?
⟨_▻EG : ∀ {i} {ℓ₁ ℓ₂} {C : Container ℓ₁} {n} {props : FVec C (Set ℓ₂) (suc n)} → proofEG props → EG {i} (FNil pre⟨ props ▻⋯)
⟨_▻EG = []EG pre⟨_▻EG

_⟩EG : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} {prop : ⟦ C ⟧ (Set ℓ₂)} → E prop → proofEG (FCons (fmap (_, FNil) prop))
(pos , proof) ⟩EG = ConsEG (pos , (proof , []EG))

_⟩EG₁ : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} {prop : ⟦ C ⟧ (Set ℓ₂)} → {pos : Position C (proj₁ prop)} → proj₂ prop pos → proofEG (FCons (fmap (_, FNil) prop))
_⟩EG₁ {pos = pos} proof = ConsEG (pos , (proof , []EG))


_▻EG_ : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} {prop : ⟦ C ⟧ (Set ℓ₂)} {n} {props : FVec C (Set ℓ₂) n} → E prop → proofEG props → proofEG (FCons (fmap (_, props) prop))
(pos , proof) ▻EG proofs = ConsEG (pos , (proof , proofs))

_▻EG₁_ : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} {prop : ⟦ C ⟧ (Set ℓ₂)} {n} {props : FVec C (Set ℓ₂) n} → {pos : Position C (proj₁ prop)} → proj₂ prop pos → proofEG props → proofEG (FCons (fmap (_, props) prop))
_▻EG₁_ {pos = pos} proof proofs = ConsEG (pos , (proof , proofs))

mapEG₁ : ∀ {i} {ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁} {A : Set ℓ₂} {f : A → Set ℓ₃} {m n} → (v : FVec C A m) → (v' : FVec C A (suc n)) → EG {i} ((vmap f v pre⟨ vmap f v' ▻⋯)) → EG {i} (map f (v pre⟨ v' ▻⋯))
proj₁ (mapEG₁ FNil (FCons x) (pos , proof)) = pos
nowE' (proj₂ (mapEG₁ FNil (FCons x) (pos , proofs))) = nowE' proofs
laterE' (proj₂ (mapEG₁ {f = f} FNil (FCons (shape , vals)) (pos , proof))) with vals pos
... | a , v = mapEG₁ v (FCons (shape , vals)) (laterE' proof)
proj₁ (mapEG₁ (FCons (proj₃ , proj₄)) v' (pos , proofs)) = pos
nowE' (proj₂ (mapEG₁ (FCons x) v' (pos , proofs))) = nowE' proofs
laterE' (proj₂ (mapEG₁ (FCons (shape , vals)) v' (pos , proofs))) with vals pos
... | a , v = mapEG₁ v v' (laterE' proofs)

mapEG : ∀ {i} {ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁} {A : Set ℓ₂} {f : A → Set ℓ₃} {m n} → {v : FVec C A m} → {v' : FVec C A (suc n)} → EG {i} ((vmap f v pre⟨ vmap f v' ▻⋯)) → EG {i} (map f (v pre⟨ v' ▻⋯))
mapEG {v = v} {v' = v'} proofs = mapEG₁ v v' proofs

bisimEG : ∀ {i} {ℓ₁ ℓ₂} {C : Container ℓ₁} {s₁ s₂ : FStream' C (Set ℓ₂)} → s₁ ∼ s₂ → EG' {i} s₁ → EG' {i} s₂
nowE' (bisimEG bisim proof) = subst (λ x → x) (hd∼ bisim) (nowE' proof)
proj₁ (laterE' (bisimEG {C = C} bisim proof))
  with laterE' proof
...  | pos , proofs = subst (Position C) (sameShapes bisim) pos
proj₂ (laterE' (bisimEG bisim proof))
  with laterE' proof
...  | pos , proofs  = bisimEG (tl∼ bisim pos) proofs

map∼ : ∀ {i} {ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁} {A : Set ℓ₂} {B : Set ℓ₃} {f : A → B} {m n} → (v : FVec C A m) → (v' : FVec C A (suc n)) → ((vmap f v pre⟨ vmap f v' ▻⋯)) ∼' (map f (v pre⟨ v' ▻⋯))
sameInitShapes (map∼ FNil (FCons x)) = refl
sameInitShapes (map∼ (FCons x) v') = refl
hd∼ (bisim (map∼ v (FCons x)) pos) = {!   !}
sameShapes (bisim (map∼ v (FCons x)) pos) = {!   !}
tl∼ (bisim (map∼ v (FCons x)) pos) = {!   !}









--

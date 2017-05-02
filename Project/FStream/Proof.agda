module FStream.Proof where

open import Data.Nat hiding (_⊔_)
open import Data.Product hiding (map)
open import Level renaming (suc to lsuc)
open import Relation.Binary.PropositionalEquality

open import FStream.Bisimulation
open import FStream.Core
open import FStream.Modalities
open import FStream.ModalitiesIdeas


data proofGA' {ℓ₁ ℓ₂} {C : Container ℓ₁} : {n : ℕ} → (props : FVec' C (Set ℓ₂) n) → Set (ℓ₁ ⊔ ℓ₂) where
  []GA' : proofGA' FNil'
  _▻GA'_ : ∀ {prop : Set ℓ₂} {n} {props : ⟦ C ⟧ (FVec' C (Set ℓ₂) n)} → prop → A (fmap proofGA' props) → proofGA' (FCons' prop props)


_preCycleGA'_ : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁} {m n} {props : FVec' C (Set ℓ₂) m} {props' : FVec' C (Set ℓ₂) (suc n)} → proofGA' props → proofGA' props' → GA' {i} (props pre⟨ props' ▻⋯')
nowA' ([]GA' preCycleGA' (proof ▻GA' _)) = proof
laterA' ([]GA' preCycleGA' (proof ▻GA' proofs)) p = (proofs p) preCycleGA' (proof ▻GA' proofs)
nowA' ((proof ▻GA' _) preCycleGA' _) = proof
laterA' ((_ ▻GA' proofs) preCycleGA' proofs') p = (proofs p) preCycleGA' proofs'

cycleGA' : ∀ {i} {ℓ₁ ℓ₂} {C : Container ℓ₁} {n} {props : FVec' C (Set ℓ₂) (suc n)} → proofGA' props → GA' {i} (FNil' pre⟨ props ▻⋯')
cycleGA' proofs = []GA' preCycleGA' proofs

data proofGA {ℓ₁ ℓ₂} {C : Container ℓ₁} : {n : ℕ} → (props : FVec C (Set ℓ₂) n) → Set (ℓ₁ ⊔ ℓ₂) where
  []GA : proofGA FNil
  ConsGA : ∀ {n} {props : ⟦ C ⟧ (Set ℓ₂ × FVec C (Set ℓ₂) n)} → A (fmap (λ x → (proj₁ x) × (proofGA (proj₂ x))) props) → proofGA (FCons props)
  -- TODO This constructor type signature is an abomination and should be somehow rewritten with proofGA, but how??
  -- TODO props should be of type FVec C (Set ℓ₂) (suc n) maybe? Or is it easier this way?



mapGA : ∀ {i} {ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁} {A : Set ℓ₂} {f : A → Set ℓ₃} {m n} → (v : FVec C A m) → (v' : FVec C A (suc n)) → GA {i} ((vmap f v pre⟨ vmap f v' ▻⋯)) → GA {i} (map f (v pre⟨ v' ▻⋯))
nowA' (mapGA FNil (FCons x) proof p) = {!   !} -- nowA' (proof p)
nowA' (mapGA (FCons x) v proof p) = {!   !} -- nowA' (proof p)
laterA' (mapGA FNil (FCons (shape , v)) proof p) p₁ = mapGA {!   !} (FCons (shape , v)) ? ?
-- laterA' (mapGA FNil v' proof p) p₁ = mapGA ({!   !}) (FCons {!   !}) (λ p₂ → laterA' (proof {!   !}) {!   !}) {!   !}
laterA' (mapGA (FCons x) v' proof p) p₁ = {!   !}


{-
mapGA : ∀ {i} {ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁} {A : Set (lsuc ℓ₃)} {f : A → Set ℓ₃} {m n} → {v : FVec C A m} → {v' : FVec C A (suc n)} → GA {i} ((vmap f v pre⟨ vmap f v' ▻⋯)) → GA {i} (map f (v pre⟨ v' ▻⋯))
nowA' (mapGA proof pos) = nowA' (proof pos)
laterA' (mapGA x p) = {!   !}
-}

_pre⟨_▻GA : ∀ {i} {ℓ₁ ℓ₂} {C : Container ℓ₁} {m n} {props : FVec C (Set ℓ₂) m} → {props' : FVec C (Set ℓ₂) (suc n)} → proofGA props → proofGA props' → GA {i} (props pre⟨ props' ▻⋯)
nowA' ( ([]GA pre⟨ (ConsGA proofs) ▻GA) p) = proj₁ (proofs p)
laterA' ( ([]GA pre⟨ (ConsGA proofs) ▻GA) p) p₁ = (proj₂ (proofs p) pre⟨ ConsGA proofs ▻GA) p₁
nowA' ( ((ConsGA proofs) pre⟨ _ ▻GA) p) = proj₁ (proofs p)
laterA' ( ((ConsGA proofs) pre⟨ proofs' ▻GA) p) p₁ = (proj₂ (proofs p) pre⟨ proofs' ▻GA) p₁
-- The p are the inputs (positions) from the side effects.

⟨_▻GA : ∀ {i} {ℓ₁ ℓ₂} {C : Container ℓ₁} {n} {props : FVec C (Set ℓ₂) (suc n)} → proofGA props → GA {i} (FNil pre⟨ props ▻⋯)
⟨_▻GA = []GA pre⟨_▻GA

-- _⟩GA : ∀ {i} {ℓ₁ ℓ₂} {C : Container ℓ₁}

data proofGE {ℓ₁ ℓ₂} {C : Container ℓ₁} : {n : ℕ} → (props : FVec C (Set ℓ₂) n) → Set (ℓ₁ ⊔ ℓ₂) where
  []GE : proofGE FNil
  ConsGE : ∀ {n} {props : ⟦ C ⟧ (Set ℓ₂ × FVec C (Set ℓ₂) n)} → E (fmap (λ x → (proj₁ x) × (proofGE (proj₂ x))) props) → proofGE (FCons props)

_pre⟨_▻GE : ∀ {i} {ℓ₁ ℓ₂} {C : Container ℓ₁} {m n} {props : FVec C (Set ℓ₂) m} → {props' : FVec C (Set ℓ₂) (suc n)} → proofGE props → proofGE props' → GE {i} (props pre⟨ props' ▻⋯)
proj₁ ([]GE pre⟨ ConsGE (pos , _) ▻GE) = pos
nowE' (proj₂ ([]GE pre⟨ ConsGE (_ , proof , _) ▻GE)) = proof
laterE' (proj₂ ([]GE pre⟨ ConsGE (pos , proof , proofs) ▻GE)) = proofs pre⟨ ConsGE (pos , proof , proofs) ▻GE
proj₁ (ConsGE (pos , _) pre⟨ _ ▻GE) = pos
nowE'   (proj₂ (ConsGE (pos , proof , proofs) pre⟨ _ ▻GE)) = proof
laterE' (proj₂ (ConsGE (_   , _     , proofs) pre⟨ v ▻GE)) = proofs pre⟨ v ▻GE

-- TODO It's worth a thought whether we want to roll our own Sigma types
-- in order to have more meaningful projector names than projᵢ


infixr 5 _▻GE_
infix 6 ⟨_▻GE
infix 7 _⟩GE

infixr 5 _▻GEᵢ_
infix 7 _⟩GEᵢ



⟨_▻GE : ∀ {i} {ℓ₁ ℓ₂} {C : Container ℓ₁} {n} {props : FVec C (Set ℓ₂) (suc n)} → proofGE props → GE {i} (FNil pre⟨ props ▻⋯)
⟨_▻GE = []GE pre⟨_▻GE

_⟩GE : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} {prop : ⟦ C ⟧ (Set ℓ₂)} → E prop → proofGE (FCons (fmap (_, FNil) prop))
(pos , proof) ⟩GE = ConsGE (pos , (proof , []GE))

_⟩GEᵢ : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} {prop : ⟦ C ⟧ (Set ℓ₂)} → {pos : Position C (proj₁ prop)} → proj₂ prop pos → proofGE (FCons (fmap (_, FNil) prop))
_⟩GEᵢ {pos = pos} proof = ConsGE (pos , (proof , []GE))


-- TODO
_▻GE_ : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} {prop : ⟦ C ⟧ (Set ℓ₂)} {n} {props : FVec C (Set ℓ₂) n} → E prop → proofGE props → proofGE (FCons (fmap (_, props) prop))
(pos , proof) ▻GE proofs = ConsGE (pos , (proof , proofs))

_▻GEᵢ_ : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} {prop : ⟦ C ⟧ (Set ℓ₂)} {n} {props : FVec C (Set ℓ₂) n} → {pos : Position C (proj₁ prop)} → proj₂ prop pos → proofGE props → proofGE (FCons (fmap (_, props) prop))
_▻GEᵢ_ {pos = pos} proof proofs = ConsGE (pos , (proof , proofs))

{-

mapGE : ∀ {i} {ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁} {A : Set ℓ₂} {f : A → Set ℓ₃} {m n} → (v : FVec C A m) → (v' : FVec C A (suc n)) → GE {i} ((vmap f v pre⟨ vmap f v' ▻⋯)) → GE {i} (map f (v pre⟨ v' ▻⋯))
proj₁ (mapGE FNil (FCons x) (pos , proof)) = pos
nowE' (proj₂ (mapGE FNil (FCons x) (pos , proof))) = {!   !}
laterE' (proj₂ (mapGE {f = f} FNil (FCons (proj₃ , proj₄)) (pos , proof))) = mapGE {! FCons ?  !} {!   !} {!   !}
proj₁ (mapGE (FCons (proj₃ , proj₄)) v' (proj₅ , proj₆)) = {!   !}
nowE' (proj₂ (mapGE (FCons x) v' (proj₃ , proj₄))) = {!   !}
laterE' (proj₂ (mapGE (FCons x) v' (proj₃ , proj₄))) = mapGE {!   !} {!   !} {!   !}

bisimGE : ∀ {i} {ℓ₁ ℓ₂} {C : Container ℓ₁} {s₁ s₂ : FStream' C (Set ℓ₂)} → s₁ ∼E s₂ → GE' {i} s₁ → GE' {i} s₂
nowE' (bisimGE bisim proof) = subst (λ x → x) (hd∼E bisim) (nowE' proof) -- TODO This thing is called differently
laterE' (bisimGE {C = C} bisim proof) = {!   !}
-}
{-
proj₁ (laterE' (bisimGE {C = C} bisim proof) {j}) = {!   !} -- subst (Position C) (sameShapesE bisim) (proj₁ (laterE' proof))
proj₂ (laterE' (bisimGE {C = C} bisim proof)) = {!   !} -- subst {! Position C  !} (sameShapesE bisim) (proj₂ (laterE' proof))
-}













--

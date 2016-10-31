module Test.EX-Predicates where

open import Data.Empty
open import Data.Unit
open import Size
open import Data.Nat
open import Data.Bool
open import Data.Vec
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Sum

open import Stream.Stream
open import RSet.RSet

open import Test.EX-Streams


isTrue : Stream Bool → RSet
isTrue x = x ≡ₛ true ▸⋯  
 
isFalse : Stream Bool → RSet
isFalse x = x ≡ₛ false ▸⋯  

isEmpty : (s1 s2 : Stream Bool) → RSet
isEmpty s1 s2 = ¬ₛ (s1 ≡ₛ s2)

alternateF : Stream Bool → RSet
alternateF x = isFalse x →ₛ ○ (isTrue x)

alternateT : Stream Bool → RSet
alternateT x = isTrue x →ₛ ○ (isFalse x)

alternates : Stream Bool → RSet
alternates x with (hd x)
... | true  = ○ (isFalse x)
... | false = ○ (isTrue x)

changesToTrue : Stream Bool → RSet
changesToTrue x = (¬ₛ isTrue x) →ₛ ○ (isTrue x)

ctt = changesToTrue

changesToFalse : Stream Bool → RSet
changesToFalse x = (¬ₛ isFalse x) →ₛ ○ (isFalse x)

hdTT : hd (isTrue TcT) 
hdTT = refl

lTT : ⟦ ⟪ Bool ⟫ ⟧
now lTT = true
later lTT = lTT

prfTT : ⟦ isTrue T-T ⟧
now prfTT = refl
later prfTT = prfTT

prfTT' : ⟦ (true ≡ true) ▸⋯ ⟧
prfTT' = refl ▹⋯

prfFF : ⟦ isFalse F-F ⟧
now prfFF = refl
later prfFF = prfFF
-- refl ▹⋯ 


prfC-lem' : ⟦ ○ (changesToTrue F-T-T) ⟧
now prfC-lem' = (λ x → refl)
later prfC-lem' = (λ x → refl) ► prfC-lem'

prfC : ⟦ changesToTrue F-T-T ⟧
now prfC x = refl
later prfC = prfC-lem'

prfC' : ⟦ changesToTrue F-T-T ⟧
prfC'  = (λ x → refl) ► prfC-lem' 

prfD : ⟦(¬ₛ (isFalse T-T)) →ₛ (isTrue T-T) ⟧
now prfD x = refl
later prfD = prfD

prfF : ⟦ (changesToTrue F-T) ⟧
now prfF p = refl
now (later prfF) p = ⊥-elim (p refl)
later (later prfF) = prfF

prfF' : ⟦ (changesToTrue T-F) ⟧
now prfF' p = ⊥-elim (p refl)
now (later prfF') x = refl
later (later prfF') = prfF'

pfG : ⟦ ¬ₛ (isTrue F-F) ⟧
now pfG ()
later pfG = pfG

prfI : ⟦ ¬ₛ (false ▸⋯ ≡ₛ true ▸⋯) ⟧
now prfI ()
later prfI = prfI

prfJ : ⟦ TcT ≡ₛ T-T ⟧
now prfJ = refl
later prfJ = prfJ

prfAND : ⟦ (isTrue T-T) ×ₛ (isFalse F-F) ⟧
now prfAND = refl , refl
later prfAND = prfAND

prfOR : ⟦ (isTrue T-T) ⊎ₛ (isTrue F-F) ⟧
now prfOR = inj₁ refl
later prfOR = prfOR

--------------------------
-- Future / eventually
--------------------------

di-lemma' : ∀ {R} → ⟦ (◇ (◇ R)) ⟧ ≡ ⟦ ◇ R ⟧
di-lemma' = {!!}

prfF1-1 : ⟦ ◇ (isTrue T-T) ⟧
now prfF1-1 = ◇-now refl
later prfF1-1 = prfF1-1

prfF1-2 :  ⟦ ◇ (isTrue F-T-T) ⟧
prfF1-2  = (◇-later {!(isTrue F-T-T)!}) ► {!!}



prfF1 : {R : RSet} → ⟦ ◇ (◇ R) →ₛ ◇ R ⟧
now prfF1 x = {!!}
later prfF1 = {!!}

--prfG1 : ⟦ □ (Bool ▸⋯) ⟧
--now prfG1 = true ▹⋯
--later prfG1 = prfG1

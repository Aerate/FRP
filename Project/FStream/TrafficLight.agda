module FStream.TrafficLight where

open import Data.Bool
open import Data.Empty
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit

open import FStream.Core
open import FStream.Containers
open import FStream.Modalities
open import FStream.Proof
open import FStream.ModalitiesIdeas
open import Relation.Binary.PropositionalEquality

data Colour : Set where
  red   : Colour
  green : Colour

_<$>_ = fmap

boolToColour : Bool → Colour
boolToColour false = green
boolToColour true = red

trafficLight : FStream (ReaderC Bool) Colour
trafficLight = ⟨ returnReader green ▻ (boolToColour <$> read) ▻ returnReader green ▻ returnReader red ⟩ ▻⋯
-- TODO Consider replacing Colour by Bool for simplification

boolLight : FStream (ReaderC Bool) Bool
boolLight = ⟨ returnReader true ▻ returnReader true ▻ returnReader false ⟩ ▻⋯

-- TODO This only proves that right now (in the first tick), liveness is satisfied, but not in the later ticks!
isLive : FA (map (_≡ green) trafficLight)
isLive = alreadyA (λ p → refl)


trafficLight₂ : FStream (ReaderC Bool) Colour
trafficLight₂ = ⟨ returnReader red ▻ (boolToColour <$> read) ▻ returnReader red ▻ returnReader green ⟩ ▻⋯
boolLight₂ : FStream (ReaderC Bool) Bool
boolLight₂ = ⟨ returnReader false ▻ returnReader false ▻ returnReader true ⟩ ▻⋯

-- FIND-OUT how to call this / what this actually means
isLive₂ : FE (map (_≡ true) boolLight₂)
isLive₂ = notYetE (true , (notYetE (true , (alreadyE (false , refl)))))


trafficLight₃ : ∀ {i} → FStream {i} (ReaderC Bool) Colour
trafficLight₃ = ⟨ returnReader green ▻ (boolToColour <$> read) ▻ returnReader red ▻ returnReader green ⟩ ▻⋯
boolLight₃ : FStream (ReaderC Bool) Bool
boolLight₃ = ⟨ returnReader true ▻ returnReader false ▻ returnReader true ⟩ ▻⋯

-- TODO: Check FAₛ implementation since only the 'AlreadyA'-Constructor seems to work
isLive₃ : ∀ {i} → head (GAₛ' {i} (FAₛ' {i} (initA {i} (map (_≡ green) (trafficLight₃ {i})))))
nowA' isLive₃ = alreadyA' (λ p → refl)
nowA' (laterA' (isLive₃ {i}) {j} p) = {!   !}
nowA' (laterA' (laterA' isLive₃ p₁) p₂) = {!   !}
nowA' (laterA' (laterA' (laterA' isLive₃ p₁) p₂) p) = {!   !}
laterA' (laterA' (laterA' (laterA' isLive₃ p₁) p₂) p) {j} p₃ = isLive₃


mutual
  -- This fellow switches between false and true every time a "true" is entered as input
  trueEgde : ∀ {i} → FStream {i} (ReaderC Bool) Bool
  proj₁ (inF trueEgde) = tt
  head (proj₂ (inF trueEgde) true) = false
  tail (proj₂ (inF trueEgde) true) = falseEgde
  head (proj₂ (inF trueEgde) false) = true
  tail (proj₂ (inF trueEgde) false) = trueEgde
  falseEgde : ∀ {i} → FStream {i} (ReaderC Bool) Bool
  proj₁ (inF falseEgde) = tt
  head (proj₂ (inF falseEgde) true) = true
  tail (proj₂ (inF falseEgde) true) = trueEgde
  head (proj₂ (inF falseEgde) false) = false
  tail (proj₂ (inF falseEgde) false) = falseEgde

-- At every point in time, it is possible (by correct input) to output true
-- TODO Not sure whether initA is called for here
mutual
  edgeResponsive : ∀ {i} → head (GAₛ' {i} (FEₛ' {i} (Eₛ {i} (map {i} (_≡ true) (trueEgde {i})))))
  nowA' edgeResponsive = alreadyE (false , refl)
  laterA' edgeResponsive false = edgeResponsive
  laterA' edgeResponsive true = edgeResponsive'
  edgeResponsive' : ∀ {i} → head (GAₛ' {i} (FEₛ' {i} (Eₛ {i} (map {i} (_≡ true) (falseEgde {i})))))
  nowA' edgeResponsive' = alreadyE (true , refl)
  laterA' edgeResponsive' false = edgeResponsive'
  laterA' edgeResponsive' true = edgeResponsive

-- Prove that a series of ⊤ is always true, under any circumstance
tautology : GA' ⟨ ⊤ ▻' returnReader FNil' ▻⋯'
-- We create a cyclical stream of proofs
tautology = cycleGA' (tt ▻GA' (λ p → []GA'))

tautology₂ : ∀ {i} → GA {i} ⟨ returnReader ⊤ ⟩ ▻⋯
nowA' (tautology₂ p) = tt
laterA' (tautology₂ p) p₁ = tautology₂ p
-- p is the position of the first side effect
{-
nowA' tautology₂ p = tt
laterA' tautology₂ p = tautology₂
-}
tautology₃ : GA ⟨ returnReader ⊤ ⟩ ▻⋯
tautology₃ = ⟨ {!   !} ▻GA

-- TODO Find something that this satisfies
identity : ∀ {A} → FStream (ReaderC A) A
identity = ⟨ read ⟩ ▻⋯

alwaysGreen : ∀ {i} → FStream {i} (ReaderC Bool) Colour
alwaysGreen = ⟨ (returnReader green) ▻ returnReader green ⟩ ▻⋯

isAlwaysGreen : ∀ {i} → GA {i} (map (_≡ green) alwaysGreen)
nowA' (isAlwaysGreen p) = refl
nowA' (laterA' (isAlwaysGreen p) p₁) = refl
laterA' (laterA' (isAlwaysGreen p) p₁) p₂ = isAlwaysGreen p
{-
nowA' isAlwaysGreen _ = refl
nowA' (laterA' isAlwaysGreen _) _ = refl
laterA' (laterA' isAlwaysGreen _) _ = isAlwaysGreen
-}

isAlwaysGreen' : ∀ {i} → GA {i} (map (_≡ green) alwaysGreen)
isAlwaysGreen' = {! cycleGA ?  !}


isGreenOrRed : ∀ {i} → GA {i} (map (λ x → (x ≡ green) ⊎ (x ≡ red)) ⟨ returnReader green ▻ returnReader red ⟩ ▻⋯)
nowA' (isGreenOrRed p) = inj₁ refl
nowA' (laterA' (isGreenOrRed p) p₁) = inj₂ refl
laterA' (laterA' (isGreenOrRed p) p₁) p₂ = isGreenOrRed p










--

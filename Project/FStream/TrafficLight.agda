module FStream.TrafficLight where

open import Data.Bool
open import Data.Empty

open import FStream.Core
open import FStream.Containers
open import FStream.Modalities
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
trafficLight = ⟨ returnReader green ▻' (boolToColour <$> read) ▻' returnReader green ▻' returnReader red ⟩ ▻⋯
boolLight : FStream (ReaderC Bool) Bool
boolLight = ⟨ returnReader true ▻' returnReader true ▻' returnReader false ⟩ ▻⋯

-- TODO This only proves that right now (in the first tick), liveness is satisfied, but not in the later ticks!
isLive : FA (map (_≡ green) trafficLight)
isLive = alreadyA (λ p → refl)


trafficLight₂ : FStream (ReaderC Bool) Colour
trafficLight₂ = ⟨ returnReader red ▻' (boolToColour <$> read) ▻' returnReader red ▻' returnReader green ⟩ ▻⋯
boolLight₂ : FStream (ReaderC Bool) Bool
boolLight₂ = ⟨ returnReader false ▻' returnReader false ▻' returnReader true ⟩ ▻⋯

-- FIND-OUT how to call this / what this actually means
isLive₂ : FE (map (_≡ true) boolLight₂)
isLive₂ = notYetE (true , (notYetE (true , (alreadyE (false , refl)))))


trafficLight₃ : FStream (ReaderC Bool) Colour
trafficLight₃ = ⟨ returnReader green ▻' (boolToColour <$> read) ▻' returnReader red ▻' returnReader green ⟩ ▻⋯
boolLight₃ : FStream (ReaderC Bool) Bool
boolLight₃ = ⟨ returnReader true ▻' returnReader false ▻' returnReader true ⟩ ▻⋯

-- TODO: Check FAₛ implementation since only the 'AlreadyA'-Constructor seems to work
isLive₃ : head (GAₛ' (FAₛ' (Aₛ (map (_≡ green) trafficLight₃))))
isLive₃ = {!!}

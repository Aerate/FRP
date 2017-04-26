module FStream.TrafficLight where

open import Data.Bool

open import FStream.Core
open import FStream.Containers
open import FStream.Modalities
open import ContainerMonkeyPatched renaming (map to fmap)
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

-- TODO This only proves that right now (in the first tick), liveness is satisfied, but not in the later ticks!
isLive : FA (map (_≡ green) trafficLight)
isLive = alreadyA (λ p → refl)

trafficLight₂ : FStream (ReaderC Bool) Bool
trafficLight₂ = ⟨ returnReader false ▻' returnReader false ▻' returnReader true ⟩ ▻⋯

-- FIND-OUT how to call this (weak liveness? - "∃π.∃t.(t c π) → φ(t,π)")
isL : FE (map (_≡ true) trafficLight₂)
isL = notYetE (true , (notYetE (true , (alreadyE (false , refl)))))

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
-- TODO Consider replacing Colour by Bool for simplification

-- TODO This only proves that right now (in the first tick), liveness is satisfied, but not in the later ticks!
isLive : FA (map (_≡ green) trafficLight)
isLive = alreadyA (λ p → refl)


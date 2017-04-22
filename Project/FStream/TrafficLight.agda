module FStream.TrafficLight where

open import Data.Bool

open import FStream.Core
open import FStream.Containers

data Colour : Set where
  red   : Colour
  green : Colour

trafficLight : FStream (ReaderC Bool) Colour
trafficLight = ⟨ returnReader green ▻' returnReader red ⟩ ▻⋯

module RSet.Examples.Crossing.TrafficLight where

open import RSet
open import RSet.Core
open import RSet.Properties.Reasoning
open import Data.Bool

module state where

data State : Set where
  green  : State
  yellow : State
  red    : State

module Ampel2 where

open import StreamNew

data Ampel : Set where
  rot   : Ampel
  gruen : Ampel

r0 : Stream Ampel
r0 = gruen ∷ {!!}

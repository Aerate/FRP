module LTL.Data.Ampel where

data Ampel : Set where
  gruen : Ampel
  rot   : Ampel

switch : Ampel → Ampel
switch gruen = rot
switch rot = gruen

notₐ = switch

module Stream.PSet where

open import Stream.Stream
open import Stream.RSet

data PSet : Set₁ where
  unOp  : RSet → PSet
  binOp : RSet → RSet → PSet

data Prop (R : RSet) : Set₁ where
  True  : PSet → Prop R
  False : Prop R

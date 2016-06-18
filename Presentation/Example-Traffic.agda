module Example-Traffic where

open import Stream
open import Data.Nat

-- states of a traffic light
data State : Set where
  red   : State
  green : State


-- flip/negate state
¬s_ : State → State
¬s red   = green
¬s green = red
infixr 8 ¬s_

-- a stream of subsequent states
-- red ▸ green ▸ red (...) || green ▸ red ▸ green (...)
StateStream : State → Stream State
hd (StateStream x) = x
tl (StateStream x) = StateStream (¬s x)


-- a traffic light has an initial state  and a stream of subsequent states 
-- that depend on init
record Light : Set where
  constructor am
  field
    init  : State
    succ  : Stream State
open Light public; L = Light


-- set initial state, get a traffic light
MakeLight : State → Light
Light.init  (MakeLight s) = s
Light.succ  (MakeLight s) = StateStream s


-- state at index n ?
_stateAt_ : L → ℕ → State
a stateAt n = (Light.succ a) at n

{-

Todo:

- show stream equality / unequality
- model intersection
- formulate constraint (as data type)
- extend to intersection states 

data Intersection (Vec Light n) : Set where

-}

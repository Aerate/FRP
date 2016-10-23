module Stream.Test.EX-Streams where

open import Stream.Stream
open import Stream.StreamEq
open import Data.Bool
open import Data.Nat
open import Data.Product
open import Stream.RSet
open import Data.Empty
open import Data.Unit
open import Data.Vec hiding (_⋎_) renaming (_∷_ to _▸_)

--Values

nats : Stream ℕ
nats = corec (λ x → x , (suc x)) 0

natz : Stream ℕ
natz = corec (str-out' nats) 0

FcT : Stream Bool
FcT = corec (λ x → x , (not x)) false
 
TcF : Stream Bool
TcF = corec (λ x → x , (not x)) true

TcT : Stream Bool
TcT =  corec (λ x → x , x) true

FcF : Stream Bool
FcF =  corec (λ x → x , x) false

F-T : Stream Bool
F-T = ⟨ false ▸ true ⟩ ▸⋯

F-T' : Stream Bool
F-T' = ⟨ false ▸ true ⟩ ▸⋯

T-F : Stream Bool
T-F = ⟨ true ▸ false ⟩ ▸⋯

T-F-F : Stream Bool
T-F-F = ⟨ true ▸ false ▸ false ⟩ ▸⋯

T-T : Stream Bool
T-T = true ▸⋯

F-F : Stream Bool
F-F = false ▸⋯

F-T-T : Stream Bool
F-T-T = false ▸ ⟨ true ▸ true ⟩ ▸⋯

repeat>F-T-T : Stream Bool
repeat>F-T-T = ⟨ false ▸ true ▸ true ⟩ ▸⋯

----------------

⊤-⊥ : RSet
⊤-⊥ =  ⟨ (⊥ ▹ ⊤) ⟩▹⋯

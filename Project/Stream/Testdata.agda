module Stream.Testdata where

open import Stream.Stream
open import Data.Bool
open import Data.Nat
open import Data.Product
open import Stream.RSet
open import Data.Empty
open import Data.Unit

--Values

FcT : Stream Bool
FcT = corec (λ x → x , (not x)) false
 
TcF : Stream Bool
TcF = corec (λ x → x , (not x)) true

TcT : Stream Bool
TcT =  corec (λ x → x , x) true

FcF : Stream Bool
FcF =  corec (λ x → x , x) false

F-T : Stream Bool
F-T = ⟨ false ▸ true ⟩▸⋯

F-T' : Stream Bool
F-T' = ⟨ false ▸ true ⟩▸⋯

T-F : Stream Bool
T-F = ⟨ true ▸ false ⟩▸⋯

⊤-⊥ : RSet
⊤-⊥ =  ⟨ (⊥ ▹ ⊤) ⟩▹⋯

T-T : Stream Bool
T-T = true ▸⋯

F-F : Stream Bool
F-F = false ▸⋯

F-T-T : Stream Bool
F-T-T = false ► ⟨ true ▸ true ⟩▸⋯

-- Types

NB : RSet
NB = ⟨ ℕ ▹ Bool ⟩▹⋯

N : RSet
N = ℕ ▹⋯


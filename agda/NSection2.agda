module NSection2 where

-- open import Data.Empty
-- open import Data.Unit
-- open import Data.Sum     hiding (map)
-- open import Data.Product hiding (map)
-- open import Data.Nat
-- open import Data.Fin
-- open import Data.Vec     renaming (map to vecMap ; foldr to vecFoldr)

-- open import Function

-- open import Relation.Binary.PropositionalEquality hiding ( [_] )

open import Level
open import Data.Unit
open import Data.Product

data Desc {ℓ : Level} : Set (suc ℓ) where
  arg : (A : Set) (d : A → Desc) → Desc
  rec : (r : Desc) → Desc
  con : (A : Set ℓ) → (r : Desc) → Desc
  ret : Desc

infix 5 ⟦_⟧_
⟦_⟧_ : {ℓ : Level} → Desc → Set ℓ → Set ℓ
⟦ arg A d ⟧ X = Σ[ a ∈ A ] ⟦ d a ⟧ X
⟦ rec d   ⟧ X = X × ⟦ d ⟧ X
⟦ con A d ⟧ X = A × ⟦ d ⟧ X
⟦ ret     ⟧ X = ⊤

data Fix (d : Desc) : Set where
  ⟨_⟩ : ⟦ d ⟧ (Fix d) → Fix d

open import Data.Nat
open import Data.Fin
open import Function

FD : ℕ → Desc
FD n = arg (Fin 5) λ { zero  {- Zero -}   → ret
                     ; (suc zero) {- K -} → con Set ret
                     ; _ → ret }

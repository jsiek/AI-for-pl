module alt.U25CrossAnchorProbe where

-- File Charter:
--   * Records the checked counterexample to the first U25 relational walk.
--   * Under U27, σ records crossing ownership and the anchor-directed
--     evaluator computes the same payload before and after re-entry.

open import Data.Fin using (zero; suc)
open import Data.Maybe using (Maybe; just)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Data.Vec.Base as Vec

open import Types
open import Primitives
open import Consistency
open import alt.ThetaTyping

empty-fresh : ∀ {Θ} {α : TyVar Θ} → α ∉ᵛ Vec.[]
empty-fresh ()

u25-source-σ : Vec.Vec (Maybe (TyVar 2)) 1
u25-source-σ = just (suc zero) Vec.∷ Vec.[]

u25-source : TyEnv 2 1 u25-source-σ
u25-source =
  ((∅ ,:= ‵ `ℕ) ,begin[ zero ≔ zero ]⟨ empty-fresh ⟩) ,:= ＇ zero

u25-target : TyEnv 2 1 u25-source-σ
u25-target =
  (u25-source ,end[ zero ])
    ,begin[ zero ≔ suc zero ]⟨ empty-fresh ⟩

-- The approved specification accepts the path: the later representation
-- `＇zero` is born while the older `suc zero` anchor is live, that type variable ends,
-- and the same anchor is immediately re-entered at `zero`.
u25-balanced : u25-source ≼[ 0 , id↪ᵗ ] u25-target
u25-balanced = ≼-end-begin refl ≼-refl ≼-refl shifted-zero

-- History: the query-specific U25 walk selected a pass case at this end and
-- got stuck because inverse weakening failed on `＇zero`.  U27 transports
-- this crossing type variable by anchor identity, so both sides compute identically.
u25-source-computes : rep? u25-source zero ≡ just (＇ zero)
u25-source-computes = refl

u25-target-computes : rep? u25-target zero ≡ just (＇ zero)
u25-target-computes = refl

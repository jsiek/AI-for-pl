module
  proof.DGG.Catchup.StructuralValueInstantiationOpenMeasureProof where

-- File Charter:
--   * Proves strict rank descent for opening a universal cast at a fresh name.
--   * Connects consistency substitution size to the generic cast-rank edge.

import Data.Fin as Fin
open import Data.Nat using (_<_; suc)
open import Types using (Ty; _[_]ᵗ; ＇_)
open import Consistency
  using (Env∼; _⊢_∼_; extᵐ; renameEnv∼; wk↪ᵗ; _[_]ᶜ)
import CastTerms as CT
open import proof.Consistency using (castSize-open-fresh-≤)
open import proof.DGG.Catchup.StructuralValueInstantiationStateDef
open import
  proof.DGG.Catchup.StructuralValueInstantiationMeasureDef
open import
  proof.DGG.Catchup.StructuralValueInstantiationAllMeasureProof
  using (all-instantiation-rank-decreases)


all-open-fresh-rank-decreases : ∀ {Δ} {μ : Env∼ Δ}
    {A B : Ty (suc (suc Δ))} {E : Ty (suc Δ)} {V}
    (vV : CT.Value { Δ = suc Δ } V)
    (d : extᵐ (renameEnv∼ wk↪ᵗ μ) ⊢ A ∼ B)
    (spine : InstantiationSpine (B [ ＇ Fin.zero ]ᵗ) E)
  → pendingAdministrationRank vV
      (cast-frame (d [ ＇ Fin.zero ]ᶜ) ▻ⁱ spine) <
      pendingAdministrationRank (vV CT.《 CT.all {c = d} 》) spine
all-open-fresh-rank-decreases vV d spine =
  all-instantiation-rank-decreases vV spine
    (castSize-open-fresh-≤ d)

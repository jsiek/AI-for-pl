module proof.NuImprecisionTargetFunctionCastSpineMeasureProof where

-- File Charter:
--   * Proves that store-change renaming preserves the function-cast rank.
--   * Proves that peeling one inert function cast strictly lowers the rank.
--   * Contains no semantic scheduling, postulate, hole, or permissive option.

open import Agda.Builtin.Equality using (_≡_; refl)
import Coercions as C
open import Data.List using ([]; _∷_)
open import Data.Nat using (_<_; suc)
open import Data.Nat.Properties using (n<1+n)
open import Relation.Binary.PropositionalEquality using (trans)

open import NuReduction using (StoreChanges; applyTerms; bind; keep)
open import NuTerms using (Term; Value; ƛ_; Λ_; $; _⟨_⟩)
open import proof.NuImprecisionTargetFunctionCastSpineMeasureDef using
  (targetFunctionCastSpineRank)
open import proof.NuTermProperties using
  (renameᵗᵐ-preserves-Value)
open import proof.ReductionProperties using
  (applyTerms-preserves-Value)
open import Types using (Renameᵗ)


target-function-cast-spine-rank-unique :
  ∀ {V : Term} (vV vV′ : Value V) →
  targetFunctionCastSpineRank vV ≡
    targetFunctionCastSpineRank vV′
target-function-cast-spine-rank-unique (ƛ N) (ƛ .N) = refl
target-function-cast-spine-rank-unique (Λ vV) (Λ vV′) =
  target-function-cast-spine-rank-unique vV vV′
target-function-cast-spine-rank-unique ($ k) ($ .k) = refl
target-function-cast-spine-rank-unique
    (vV ⟨ inert ⟩) (vV′ ⟨ inert′ ⟩)
  rewrite target-function-cast-spine-rank-unique vV vV′ = refl


target-function-cast-spine-rank-rename :
  ∀ (ρ : Renameᵗ) {V : Term} (vV : Value V) →
  targetFunctionCastSpineRank
      (renameᵗᵐ-preserves-Value ρ vV) ≡
    targetFunctionCastSpineRank vV
target-function-cast-spine-rank-rename ρ (ƛ N) = refl
target-function-cast-spine-rank-rename ρ (Λ vV) =
  target-function-cast-spine-rank-rename _ vV
target-function-cast-spine-rank-rename ρ ($ k) = refl
target-function-cast-spine-rank-rename ρ (vV ⟨ inert ⟩)
  rewrite target-function-cast-spine-rank-rename ρ vV = refl


target-function-cast-spine-rank-applyTerms :
  ∀ (χs : StoreChanges) {V : Term} (vV : Value V) →
  targetFunctionCastSpineRank
      (applyTerms-preserves-Value χs vV) ≡
    targetFunctionCastSpineRank vV
target-function-cast-spine-rank-applyTerms [] vV = refl
target-function-cast-spine-rank-applyTerms (keep ∷ χs) vV =
  target-function-cast-spine-rank-applyTerms χs vV
target-function-cast-spine-rank-applyTerms (bind A ∷ χs) vV =
  trans
    (target-function-cast-spine-rank-applyTerms χs
      (renameᵗᵐ-preserves-Value _ vV))
    (target-function-cast-spine-rank-rename _ vV)


target-function-cast-spine-rank-decreases :
  ∀ {W : Term} (vW : Value W) c d →
  targetFunctionCastSpineRank vW <
    targetFunctionCastSpineRank (vW ⟨ c C.↦ d ⟩)
target-function-cast-spine-rank-decreases vW c d =
  n<1+n (targetFunctionCastSpineRank vW)

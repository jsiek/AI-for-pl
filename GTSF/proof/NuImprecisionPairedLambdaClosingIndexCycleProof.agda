module proof.NuImprecisionPairedLambdaClosingIndexCycleProof where

-- File Charter:
--   * Reduces the exact paired-lambda closing index cycle to the reusable
--     common-target-extension obstruction.
--   * Opens the unused matched binder on both endpoints, cancels both lifts,
--     and pairs the resulting lower bounds in one span.
--   * Contains no canonical dependency assembly, conversion, store, term
--     relation, simulation, postulate, hole, or permissive option.

open import Agda.Builtin.Equality using (refl)
open import Data.Nat using (suc; zero)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import Relation.Binary.PropositionalEquality using (subst)
open import Types using (occurs; singleRenameᵗ; renameᵗ; `∀; ⇑ᵗ)
open import proof.EndpointCanonicalMLBSimplePairedSpan using
  (pair-lower; span)
open import proof.MaximalLowerBoundsWf using (open-unused-bothᵢ)
open import proof.NuImprecisionCommonTargetExtensionCycleDef using
  (CommonTargetExtensionCycleᵀ)
open import proof.NuImprecisionPairedLambdaClosingIndexCycleDef using
  (PairedLambdaClosingIndexCycleᵀ)
open import proof.TypeProperties using
  (occurs-raise-fresh; renameᵗ-single-suc-cancel)


paired-lambda-closing-index-cycle-proofᵀ :
  CommonTargetExtensionCycleᵀ →
  PairedLambdaClosingIndexCycleᵀ
paired-lambda-closing-index-cycle-proofᵀ common
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {F = F} {X′ = X′}
    refl q p =
  common (pair-lower q-down p)
  where
  opened =
    open-unused-bothᵢ
      (occurs-raise-fresh zero (`∀ F))
      (occurs-raise-fresh zero X′)
      q

  target-down =
    subst
      (λ T → Φ ∣ Δᴸ
        ⊢ renameᵗ (singleRenameᵗ zero) (⇑ᵗ (`∀ F)) ⊑ T
        ⊣ Δᴿ)
      (renameᵗ-single-suc-cancel zero X′)
      opened

  q-down =
    subst
      (λ S → Φ ∣ Δᴸ ⊢ S ⊑ X′ ⊣ Δᴿ)
      (renameᵗ-single-suc-cancel zero (`∀ F))
      target-down

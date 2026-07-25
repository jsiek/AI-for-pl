module
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentSourceKeepOutcomeComposition
  where

-- File Charter:
--   * Prepends one source `keep` step to a world-coherent target-oriented
--     one-step outcome.
--   * Uses the supplied pre-recursion relation to make the source step a
--     left-silent prefix with reflexive relational-store lineage.
--   * Preserves every final-world invariant and propagates source blame.
--   * Contains no recursive dispatcher, postulate, hole, permissive option,
--     or compatibility wrapper.

open import Agda.Builtin.Equality using (refl)
open import Data.List using ([])
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuReduction using (StoreChange; keep; _—→[_]_)
open import NuTermImprecision using (StoreImp)
open import NuTerms using (RuntimeOK)
open import QuotientedTermImprecision using
  ( prefix-reflⁱ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import proof.Catchup.Core.NuImprecisionCatchupComposition using
  ( weak-one-step-keep-source-catchup-type-coherenceᵀ
  ; weak-one-step-keep-source-catchup-transportᵀ
  ; weak-one-step-keep-source-catchupᵀ
  )
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  ( left-silent-indexed
  ; left-silent-invariant
  ; weak-indexed-result
  )
open import
  proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef
  using (weak-step-store-lineage)
open import
  proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingAlgebra
  using (rel-store-embedding-reflⁱ)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentLeftSilentOutcomeComposition
  using (world-coherent-left-silent-then-outcomeᵀ)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using (WorldCoherentWeakOneStepIndexedOutcome)


world-coherent-source-keep-then-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ M L M′ N′ A B}
    {χ : StoreChange}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  RuntimeOK L →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ L ⊑ M′ ⦂ A ⊑ B ∶ p →
  M —→[ keep ] L →
  WorldCoherentWeakOneStepIndexedOutcome
    {M = L} {N′ = N′} {χ = χ} {ρ = ρ} p →
  WorldCoherentWeakOneStepIndexedOutcome
    {M = M} {N′ = N′} {χ = χ} {ρ = ρ} p
world-coherent-source-keep-then-outcomeᵀ
    {ρ = ρ} okL L⊑M′ source→ outcome =
  world-coherent-left-silent-then-outcomeᵀ
    silent lineage outcome
  where
  raw = weak-one-step-keep-source-catchupᵀ source→ L⊑M′

  indexed =
    weak-indexed-result raw L⊑M′
      (weak-one-step-keep-source-catchup-transportᵀ source→ L⊑M′)
      (weak-one-step-keep-source-catchup-type-coherenceᵀ source→ L⊑M′)

  silent =
    left-silent-indexed indexed
      (left-silent-invariant refl refl) okL

  lineage =
    weak-step-store-lineage
      ρ rel-store-embedding-reflⁱ prefix-reflⁱ

module
  proof.Right.StorePrefix.NuImprecisionRightOnlyStoreLineageCompositionDef
  where

-- File Charter:
--   * Defines composition of weak-step store lineages whose allocation
--     prefixes contain only target entries.
--   * Exposes both the ordinary composed lineage and its stronger right-only
--     prefix witness.
--   * Contains no implementation, term simulation, postulate, hole,
--     permissive option, or broad DGG import.

open import Data.Product using (Σ-syntax)

open import NuReduction using (_—→[_]_)
open import NuTermImprecision using (StoreImp)
open import NuTerms using (Term)
open import Types using (Ty)
open import proof.Right.StorePrefix.NuImprecisionRightOnlyStorePrefix using
  (RightOnlyStoreImpPrefix)
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  ( WeakOneStepResult
  ; resultStore
  ; sourceResult
  ; targetResult
  )
open import proof.Catchup.Simulation.NuImprecisionSimulationCore using
  (weak-one-step-composeᵀ)
open import proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef using
  (WeakOneStepStoreLineage; lineageStore)


WeakOneStepRightOnlyStoreLineageCompositionᵀ : Set₁
WeakOneStepRightOnlyStoreLineageCompositionᵀ =
  ∀ {Φ Δᴸ Δᴿ M M′ A B χ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (first : WeakOneStepResult ρ M M′ A B χ)
    {χ′ N′}
    (target→ : targetResult first —→[ χ′ ] N′)
    (second : WeakOneStepResult
      (resultStore first) (sourceResult first) N′
      _ _ χ′)
    (first-lineage : WeakOneStepStoreLineage first)
    (second-lineage : WeakOneStepStoreLineage second) →
  RightOnlyStoreImpPrefix
    (lineageStore first-lineage) (resultStore first) →
  RightOnlyStoreImpPrefix
    (lineageStore second-lineage) (resultStore second) →
  Σ[ combined-lineage ∈
    WeakOneStepStoreLineage
      (weak-one-step-composeᵀ first target→ second) ]
    RightOnlyStoreImpPrefix
      (lineageStore combined-lineage)
      (resultStore
        (weak-one-step-composeᵀ first target→ second))

module proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef where

-- File Charter:
--   * Defines relational-store lineage for a weak one-step result.
--   * Factors lineage into renaming of every old relational entry followed
--     by a prefix of newly allocated entries.
--   * Contains no simulation, lineage construction, transport contract,
--     theorem-fragment alias, or transport proof.

open import Data.List using (_∷_)

open import NuReduction using (applyTys)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  (StoreImp)
open import QuotientedTermImprecision using
  (StoreImpPrefix)
open import proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingDef using
  (RelStoreEmbeddingⁱ)
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  ( WeakOneStepResult
  ; resultCtx
  ; resultLeftCtx
  ; resultRightCtx
  ; resultStore
  ; sourceChanges
  ; targetTailChanges
  )
open import proof.Core.Properties.ReductionProperties using
  (applyTyVars)


record WeakOneStepStoreLineage
    {Φ Δᴸ Δᴿ M N′ A B χ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (result : WeakOneStepResult ρ M N′ A B χ) : Set₁ where
  constructor weak-step-store-lineage
  field
    lineageStore :
      StoreImp
        (resultCtx result)
        (resultLeftCtx result)
        (resultRightCtx result)

    lineageEmbedding :
      RelStoreEmbeddingⁱ
        (applyTyVars (sourceChanges result))
        (applyTyVars (χ ∷ targetTailChanges result))
        ρ lineageStore

    lineagePrefix :
      StoreImpPrefix lineageStore (resultStore result)

open WeakOneStepStoreLineage public

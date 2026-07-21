module proof.NuImprecisionWorldCoherentSourceOneStepResultDef where

-- File Charter:
--   * Defines the exact continuing result for source-oriented one-step
--     simulation.
--   * Retains generic transport, type coherence, store lineage, and final
--     world invariants needed to rebuild evaluation contexts.
--   * Records that the source trace is exactly the distinguished source step.
--   * Contains no implementation, postulate, hole, or permissive option.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using ([]; _∷_)

open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuReduction using (StoreChange; keep)
open import NuTermImprecision using (StoreImp)
open import proof.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuImprecisionSimulationResultDef using
  ( WeakOneStepIndexedResult
  ; WeakOneStepTransport
  ; WeakOneStepTypeCoherence
  ; resultCtx
  ; resultStore
  ; sourceChanges
  ; sourceResult
  ; weakIndexedResult
  )
open import proof.NuImprecisionWeakOneStepStoreLineageDef using
  (WeakOneStepStoreLineage)
open import proof.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)


record WorldCoherentSourceOneStepIndexedResult
    {Φ Δᴸ Δᴿ M M′ L A B}
    {χ : StoreChange}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ) : Set₁ where
  constructor world-coherent-source-one-step-indexed
  field
    sourceStepIndexedResult :
      WeakOneStepIndexedResult
        {M = M} {N′ = M′} {χ = keep} {ρ = ρ} p

    sourceStepTransport :
      WeakOneStepTransport
        (weakIndexedResult sourceStepIndexedResult)

    sourceStepTypeCoherence :
      WeakOneStepTypeCoherence
        (weakIndexedResult sourceStepIndexedResult)

    sourceStepStoreLineage :
      WeakOneStepStoreLineage
        (weakIndexedResult sourceStepIndexedResult)

    sourceStepChangesExact :
      sourceChanges
        (weakIndexedResult sourceStepIndexedResult) ≡ χ ∷ []

    sourceStepResultExact :
      sourceResult
        (weakIndexedResult sourceStepIndexedResult) ≡ L

    sourceStepWorldCoherent :
      WorldCoherent
        (resultStore
          (weakIndexedResult sourceStepIndexedResult))

    sourceStepSourceNameExclusive :
      SourceNameExclusive
        (resultCtx
          (weakIndexedResult sourceStepIndexedResult))

open WorldCoherentSourceOneStepIndexedResult public

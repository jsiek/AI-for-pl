module
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentLeftCatchupPrependKeepStep
  where

-- File Charter:
--   * Owns administrative source keep-step prepending for world-coherent
--     left catch-up results.
--   * Provides the lifted post-allocation `β-Λ•` step used by source-only
--     ordinary and dynamic `ν` target-closing proofs.
--   * Contains no semantic catch-up dispatcher or permissive option.

open import Agda.Builtin.Equality using (refl)
open import Data.List using (_∷_)
open import Data.Nat using (suc)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuReduction using
  ( keep
  ; pure-step
  ; ξ-⟨⟩
  ; β-Λ•
  ; ↠-step
  ; _—→[_]_
  )
open import NuTermImprecision using (StoreImp)
open import NuTerms using (Term; Value; Λ_; ⇑ᵗᵐ; _•; _⟨_⟩)
open import Relation.Binary.PropositionalEquality using (subst)
open import Types using (extᵗ)
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  ( WeakOneStepResult
  ; left-catchup-invariant
  ; left-indexed-catchup
  ; left-silent-invariant
  ; relatedResults
  ; resultCtx
  ; resultLeftCtx
  ; resultRightCtx
  ; resultSourceType
  ; resultStore
  ; resultTargetType
  ; resultType
  ; sourceCatchup
  ; sourceChanges
  ; sourceCtxResult
  ; sourceResult
  ; sourceStoreResult
  ; sourceTypeResult
  ; targetCtxResult
  ; targetResult
  ; targetStoreResult
  ; targetTail
  ; targetTailChanges
  ; targetTypeResult
  ; transportAllBody
  ; transportRightBody
  ; transportType
  ; weak-indexed-result
  ; weak-step-transport
  ; weak-step-type-coherence
  )
open import proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef using
  (weak-step-store-lineage)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef using
  ( WorldCoherentLeftCatchupIndexedResult
  ; world-coherent-left-indexed-catchup
  )
open import proof.Core.Properties.NuTermProperties using
  (open0-ext-suc-cancelᵐ; renameᵗᵐ-preserves-Value)


post-allocation-β-Λ-cast :
  ∀ {W s} →
  Value W →
  ((⇑ᵗᵐ (Λ W)) •) ⟨ s ⟩ —→[ keep ] W ⟨ s ⟩
post-allocation-β-Λ-cast {W = W} vW =
  ξ-⟨⟩
    (subst
      (λ N → (⇑ᵗᵐ (Λ W)) • —→[ keep ] N)
      (open0-ext-suc-cancelᵐ W)
      (pure-step
        (β-Λ• (renameᵗᵐ-preserves-Value (extᵗ suc) vW))))


prepend-left-keep-step-result :
  ∀ {Φ Δᴸ Δᴿ M N V′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  M —→[ keep ] N →
  WeakOneStepResult ρ N V′ A B keep →
  WeakOneStepResult ρ M V′ A B keep
prepend-left-keep-step-result source→ result =
  record
    { sourceChanges = keep ∷ sourceChanges result
    ; targetTailChanges = targetTailChanges result
    ; sourceResult = sourceResult result
    ; targetResult = targetResult result
    ; resultCtx = resultCtx result
    ; resultLeftCtx = resultLeftCtx result
    ; resultRightCtx = resultRightCtx result
    ; sourceCtxResult = sourceCtxResult result
    ; targetCtxResult = targetCtxResult result
    ; resultStore = resultStore result
    ; resultSourceType = resultSourceType result
    ; resultTargetType = resultTargetType result
    ; sourceTypeResult = sourceTypeResult result
    ; targetTypeResult = targetTypeResult result
    ; transportType = transportType result
    ; transportAllBody = transportAllBody result
    ; transportRightBody = transportRightBody result
    ; resultType = resultType result
    ; sourceCatchup = ↠-step source→ (sourceCatchup result)
    ; targetTail = targetTail result
    ; sourceStoreResult = sourceStoreResult result
    ; targetStoreResult = targetStoreResult result
    ; relatedResults = relatedResults result
    }


world-coherent-left-catchup-prepend-keep-step :
  ∀ {Φ Δᴸ Δᴿ M N V′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  M —→[ keep ] N →
  WorldCoherentLeftCatchupIndexedResult
    {N = N} {V′ = V′} {ρ = ρ} p →
  WorldCoherentLeftCatchupIndexedResult
    {N = M} {V′ = V′} {ρ = ρ} p
world-coherent-left-catchup-prepend-keep-step
    source→
    (world-coherent-left-indexed-catchup
      (left-indexed-catchup
        (weak-indexed-result result canonical
          (weak-step-transport transport)
          (weak-step-type-coherence arrow all))
        (left-catchup-invariant (left-silent-invariant refl refl) final))
      (weak-step-store-lineage lineage-store lineage-embedding
        lineage-prefix)
      coherent exclusive wfL) =
  world-coherent-left-indexed-catchup
    (left-indexed-catchup
      (weak-indexed-result prefixed canonical
        (weak-step-transport transport)
        (weak-step-type-coherence arrow all))
      (left-catchup-invariant (left-silent-invariant refl refl) final))
    (weak-step-store-lineage lineage-store lineage-embedding
      lineage-prefix)
    coherent exclusive wfL
  where
  prefixed = prepend-left-keep-step-result source→ result

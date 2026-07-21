module proof.NuImprecisionSourceSilentCompositionDef where

-- File Charter:
--   * Defines composition of a source-silent target catch-up with a following
--     exact source-oriented result.
--   * Requires the composed result to preserve generic term transport,
--     arrow/`∀` type coherence, and relational-store lineage.
--   * Contains no composition implementation, postulate, or hole.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using ([])

open import NuReduction using (keep)
open import NuTermImprecision using (StoreImp)
open import proof.NuImprecisionSimulationResultDef using
  ( WeakOneStepResult
  ; WeakOneStepTransport
  ; WeakOneStepTypeCoherence
  ; resultSourceType
  ; resultStore
  ; resultTargetType
  ; sourceChanges
  ; sourceResult
  ; targetResult
  )
open import proof.NuImprecisionWeakOneStepStoreLineageDef using
  (WeakOneStepStoreLineage)


record SourceSilentComposition : Set₁ where
  field
    sourceSilentResult :
      ∀ {Φ Δᴸ Δᴿ M M′ A B}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        (first : WeakOneStepResult ρ M M′ A B keep) →
      sourceChanges first ≡ [] →
      sourceResult first ≡ M →
      (second : WeakOneStepResult
        (resultStore first)
        (sourceResult first)
        (targetResult first)
        (resultSourceType first)
        (resultTargetType first)
        keep) →
      WeakOneStepResult ρ M M′ A B keep

    sourceSilentTransport :
      ∀ {Φ Δᴸ Δᴿ M M′ A B}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        (first : WeakOneStepResult ρ M M′ A B keep)
        (source-empty : sourceChanges first ≡ [])
        (source-same : sourceResult first ≡ M)
        (second : WeakOneStepResult
          (resultStore first)
          (sourceResult first)
          (targetResult first)
          (resultSourceType first)
          (resultTargetType first)
          keep) →
      WeakOneStepTransport first →
      WeakOneStepTransport second →
      WeakOneStepTransport
        (sourceSilentResult first source-empty source-same second)

    sourceSilentTypeCoherence :
      ∀ {Φ Δᴸ Δᴿ M M′ A B}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        (first : WeakOneStepResult ρ M M′ A B keep)
        (source-empty : sourceChanges first ≡ [])
        (source-same : sourceResult first ≡ M)
        (second : WeakOneStepResult
          (resultStore first)
          (sourceResult first)
          (targetResult first)
          (resultSourceType first)
          (resultTargetType first)
          keep) →
      WeakOneStepTypeCoherence first →
      WeakOneStepTypeCoherence second →
      WeakOneStepTypeCoherence
        (sourceSilentResult first source-empty source-same second)

    sourceSilentStoreLineage :
      ∀ {Φ Δᴸ Δᴿ M M′ A B}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        (first : WeakOneStepResult ρ M M′ A B keep)
        (source-empty : sourceChanges first ≡ [])
        (source-same : sourceResult first ≡ M)
        (second : WeakOneStepResult
          (resultStore first)
          (sourceResult first)
          (targetResult first)
          (resultSourceType first)
          (resultTargetType first)
          keep) →
      WeakOneStepStoreLineage first →
      WeakOneStepStoreLineage second →
      WeakOneStepStoreLineage
        (sourceSilentResult first source-empty source-same second)

open SourceSilentComposition public

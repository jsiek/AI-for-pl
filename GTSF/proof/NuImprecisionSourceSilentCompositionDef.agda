module proof.NuImprecisionSourceSilentCompositionDef where

-- File Charter:
--   * Defines composition of a source-silent target catch-up with a following
--     exact source-oriented result.
--   * Requires the composed result to preserve generic term transport,
--     arrow/`∀` type coherence, relational-store lineage, and final context
--     uniqueness.
--   * Contains no composition implementation, postulate, or hole.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using ([])

open import NuReduction using (StoreChanges; keep)
open import NuTermImprecision using (StoreImp)
open import NuTerms using (Term)
open import proof.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import proof.NuImprecisionSimulationResultDef using
  ( WeakOneStepResult
  ; WeakOneStepTransport
  ; WeakOneStepTypeCoherence
  ; resultSourceType
  ; resultCtx
  ; resultStore
  ; resultTargetType
  ; sourceChanges
  ; sourceResult
  ; targetResult
  )
open import proof.NuImprecisionWeakOneStepStoreLineageDef using
  (WeakOneStepStoreLineage)
open import proof.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)


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

    sourceSilentChangesExact :
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
          keep)
        {χs : StoreChanges} →
      sourceChanges second ≡ χs →
      sourceChanges
        (sourceSilentResult first source-empty source-same second) ≡ χs

    sourceSilentResultExact :
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
          keep)
        {L : Term} →
      sourceResult second ≡ L →
      sourceResult
        (sourceSilentResult first source-empty source-same second) ≡ L

    sourceSilentWorldCoherent :
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
      WorldCoherent (resultStore second) →
      WorldCoherent
        (resultStore
          (sourceSilentResult first source-empty source-same second))

    sourceSilentSourceNameExclusive :
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
      SourceNameExclusive (resultCtx second) →
      SourceNameExclusive
        (resultCtx
          (sourceSilentResult first source-empty source-same second))

    sourceSilentAssumptionMembershipUnique :
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
      AssumptionMembershipUnique (resultCtx second) →
      AssumptionMembershipUnique
        (resultCtx
          (sourceSilentResult first source-empty source-same second))

open SourceSilentComposition public

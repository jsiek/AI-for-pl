module
  proof.WorldCoherent.Right.Target.Resume.NuImprecisionWorldCoherentRightTargetSilentContinuationContextProof
  where

-- File Charter:
--   * Composes two exact-endpoint world-coherent right-value catch-ups using
--     the canonical lower-level source-silent composition capability.
--   * Composes target-context actions, right-only store lineage, and the
--     source-bullet transport invariant without an intervening target step.
--   * Contains no recursive dispatcher, new result carrier, postulate, hole,
--     permissive option, termination bypass, or broad DGG import.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _++_)
open import Data.Product using (_,_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)

open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuReduction using
  (applyTerm; applyTerms; applyTy; applyTys; keep)
open import NuTermImprecision using (StoreImp)
open import NuTerms using (Term)
open import QuotientedTermImprecision using
  (prefix-reflⁱ; nu-term-imprecision-source-typing)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessLemma
  using (assumption-membership-unique→precision-index-unique)
open import
  proof.Right.Core.NuImprecisionRightContextAction
  using
  ( applyRightImpCtxChanges
  ; applyRightImpCtxChanges-++
  )
open import
  proof.Right.StorePrefix.NuImprecisionRightOnlyStorePrefix
  using
  ( RightOnlyStoreImpPrefix
  ; right-only-store-prefix
  )
open import
  proof.Right.StorePrefix.NuImprecisionRightOnlyStorePrefixAlgebra
  using
  ( rel-store-embedding-right-only-prefix-invⁱ
  ; right-only-store-prefix-transⁱ
  )
open import
  proof.Right.ValueCatchup.NuImprecisionRightValueCatchupResultDef
  using
  ( right-value-indexed-catchup
  ; rightCatchupIndexedResult
  ; rightCatchupSourceChangesEmpty
  ; rightCatchupSourceNoBullet
  ; rightCatchupSourceUnchanged
  ; rightCatchupSourceValue
  ; rightCatchupTargetNoBullet
  ; rightCatchupTargetValue
  )
open import
  proof.Right.ValueCatchup.NuImprecisionRightValueCatchupSourceBulletTransportDef
  using (RightValueCatchupSourceBulletTransportᵀ)
open import
  proof.Catchup.Simulation.NuImprecisionSimulationCore
  using
  ( nu-term-imprecision-transport-termsᵀ
  ; nu-term-imprecision-transport-typesᵀ
  ; weak-one-step-index-resultᵀ
  ; weak-one-step-reindex-preserves-transportᵀ
  ; weak-one-step-reindex-preserves-type-coherenceᵀ
  ; weak-one-step-reindexᵀ
  )
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  ( WeakOneStepResult
  ; canonicalIndexedResults
  ; resultCtx
  ; resultLeftCtx
  ; resultRightCtx
  ; resultSourceType
  ; resultStore
  ; resultTargetType
  ; resultType
  ; sourceChanges
  ; sourceResult
  ; sourceTypeResult
  ; targetTailChanges
  ; targetTypeResult
  ; transportType
  ; weakIndexedResult
  ; weakIndexedTransport
  ; weakIndexedTypeCoherence
  )
open import
  proof.Source.Core.NuImprecisionSourceSilentCompositionProof
  using
  ( source-silent-preserves-changes-exactᵀ
  ; source-silent-preserves-result-exactᵀ
  ; source-silent-preserves-transportᵀ
  ; source-silent-preserves-type-coherenceᵀ
  ; source-silent-resultᵀ
  )
open import
  proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef
  using
  ( WeakOneStepStoreLineage
  ; lineageEmbedding
  ; lineagePrefix
  ; lineageStore
  ; weak-step-store-lineage
  )
open import
  proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingAlgebra
  using
  ( rel-store-embedding-composeⁱ
  ; rel-store-embedding-congⁱ
  )
open import
  proof.Core.Properties.ReductionProperties
  using
  ( applyTerms-++
  ; applyTerms-preserves-No•
  ; applyTys-++
  ; applyTyVars-++
  )
open import Types using (Ty; TyCtx)
open import
  proof.WorldCoherent.Right.Target.Resume.NuImprecisionWorldCoherentRightTargetSilentContinuationContextDef
  using (WorldCoherentRightTargetSilentContinuationContextᵀ)
open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightCatchupResultDef
  using
  ( WorldCoherentRightValueCatchupIndexedResult
  ; world-coherent-right-value-indexed-catchup
  ; worldRightCatchupAssumptionMembershipUnique
  ; worldRightCatchupCoherence
  ; worldRightCatchupResult
  ; worldRightCatchupSourceBulletTransport
  ; worldRightCatchupSourceNameExclusive
  ; worldRightCatchupStoreLineage
  ; worldRightCatchupTargetStoreWf
  )


private
  canonical-right-catchup-result :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {V M′ : Term} {A B : Ty}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    WorldCoherentRightValueCatchupIndexedResult
      {V = V} {M′ = M′} {ρ = ρ} p →
    WeakOneStepResult ρ V M′ A B keep
  canonical-right-catchup-result caught =
    weak-one-step-reindexᵀ raw refl refl
      (canonicalIndexedResults indexed)
    where
    indexed =
      rightCatchupIndexedResult (worldRightCatchupResult caught)
    raw = weakIndexedResult indexed


  canonical-right-catchup-lineage :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {V M′ : Term} {A B : Ty}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
      (caught : WorldCoherentRightValueCatchupIndexedResult
        {V = V} {M′ = M′} {ρ = ρ} p) →
    WeakOneStepStoreLineage
      (canonical-right-catchup-result caught)
  canonical-right-catchup-lineage caught =
    weak-step-store-lineage
      (lineageStore original)
      (lineageEmbedding original)
      (lineagePrefix original)
    where
    original = worldRightCatchupStoreLineage caught


  source-silent-right-only-store-lineage :
    ∀ {Φ Δᴸ Δᴿ M M′ A B}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      (first : WeakOneStepResult ρ M M′ A B keep)
      (source-empty : sourceChanges first ≡ [])
      (source-same : sourceResult first ≡ M)
      (second : WeakOneStepResult
        (resultStore first)
        (sourceResult first)
        _
        (resultSourceType first)
        (resultTargetType first)
        keep)
      (first-lineage : WeakOneStepStoreLineage first)
      (second-lineage : WeakOneStepStoreLineage second) →
    RightOnlyStoreImpPrefix
      (lineageStore first-lineage) (resultStore first) →
    RightOnlyStoreImpPrefix
      (lineageStore second-lineage) (resultStore second) →
    Σ[ combined-lineage ∈
      WeakOneStepStoreLineage
        (source-silent-resultᵀ first source-empty source-same second) ]
      RightOnlyStoreImpPrefix
        (lineageStore combined-lineage)
        (resultStore
          (source-silent-resultᵀ first source-empty source-same second))
  source-silent-right-only-store-lineage
      first refl refl second
      first-lineage second-lineage first-prefix second-prefix
      with rel-store-embedding-right-only-prefix-invⁱ
        first-prefix (lineageEmbedding second-lineage)
  source-silent-right-only-store-lineage
      first refl refl second
      first-lineage second-lineage first-prefix second-prefix
      | store₁₂ , embedding₁₂ , prefix₁₂ =
    weak-step-store-lineage
        store₁₂ combined-embedding
        (right-only-store-prefix combined-prefix) ,
      combined-prefix
    where
    combined-embedding =
      rel-store-embedding-congⁱ
        (λ α → sym
          (applyTyVars-++
            (sourceChanges first) (sourceChanges second) α))
        (λ β → sym
          (applyTyVars-++
            (targetTailChanges first)
            (targetTailChanges second) β))
        (rel-store-embedding-composeⁱ
          (lineageEmbedding first-lineage) embedding₁₂)

    combined-prefix =
      right-only-store-prefix-transⁱ prefix₁₂ second-prefix


  source-silent-source-bullet-transport :
    ∀ {Φ Δᴸ Δᴿ M M′ A B}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      (first : WeakOneStepResult ρ M M′ A B keep)
      (source-empty : sourceChanges first ≡ [])
      (source-same : sourceResult first ≡ M)
      (second : WeakOneStepResult
        (resultStore first)
        (sourceResult first)
        _
        (resultSourceType first)
        (resultTargetType first)
        keep) →
    sourceChanges second ≡ [] →
    RightValueCatchupSourceBulletTransportᵀ first →
    RightValueCatchupSourceBulletTransportᵀ second →
    RightValueCatchupSourceBulletTransportᵀ
      (source-silent-resultᵀ first source-empty source-same second)
  source-silent-source-bullet-transport
      first refl refl second refl first-bullet second-bullet
      {L = L} {M′ = M′} {C = C} {C′ = C′}
      prefix okL noM′ L⊢ L⊑M′ =
    nu-term-imprecision-transport-termsᵀ
      refl
      (sym (applyTerms-++
        (targetTailChanges first)
        (targetTailChanges second)
        (applyTerm keep M′)))
      (nu-term-imprecision-transport-typesᵀ
        (sym (applyTys-++ [] [] C))
        (sym (applyTys-++
          (targetTailChanges first)
          (targetTailChanges second)
          (applyTy keep C′)))
        refl
        second-relation)
    where
    first-relation =
      first-bullet prefix okL noM′ L⊢ L⊑M′

    second-relation =
      second-bullet
        prefix-reflⁱ
        okL
        (applyTerms-preserves-No•
          (targetTailChanges first) noM′)
        (nu-term-imprecision-source-typing first-relation)
        first-relation


world-coherent-right-target-silent-continuation-context-proofᵀ :
  WorldCoherentRightTargetSilentContinuationContextᵀ
world-coherent-right-target-silent-continuation-context-proofᵀ
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {ρ = ρ}
    {V = V} {M′ = M′} {A = A} {B = B}
    first-world first-context first-prefix
    second-world second-context second-prefix
    with rightCatchupSourceChangesEmpty
      (worldRightCatchupResult first-world)
       | rightCatchupSourceUnchanged
      (worldRightCatchupResult first-world)
world-coherent-right-target-silent-continuation-context-proofᵀ
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {ρ = ρ}
    {V = V} {M′ = M′} {A = A} {B = B}
    first-world first-context first-prefix
    second-world second-context second-prefix
    | refl | refl
    with source-silent-right-only-store-lineage
      {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {ρ = ρ}
      (canonical-right-catchup-result first-world)
      refl refl
      (weakIndexedResult
        (rightCatchupIndexedResult
          (worldRightCatchupResult second-world)))
      (canonical-right-catchup-lineage first-world)
      (worldRightCatchupStoreLineage second-world)
      first-prefix second-prefix
world-coherent-right-target-silent-continuation-context-proofᵀ
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {ρ = ρ}
    {V = V} {M′ = M′} {A = A} {B = B}
    first-world first-context first-prefix
    second-world second-context second-prefix
    | refl | refl | combined-lineage , combined-prefix =
  world-coherent-right-value-indexed-catchup
      (right-value-indexed-catchup
        combined-indexed combined-source-empty combined-source-same
        (rightCatchupSourceValue first-catchup)
        (rightCatchupSourceNoBullet first-catchup)
        (rightCatchupTargetValue second-catchup)
        (rightCatchupTargetNoBullet second-catchup))
      combined-lineage combined-bullet
      (worldRightCatchupCoherence second-world)
      (worldRightCatchupSourceNameExclusive second-world)
      combined-unique
      (worldRightCatchupTargetStoreWf second-world) ,
    combined-context ,
    combined-prefix
  where
  first-catchup = worldRightCatchupResult first-world
  first-indexed = rightCatchupIndexedResult first-catchup
  first-raw = weakIndexedResult first-indexed
  first-related = canonicalIndexedResults first-indexed
  first = canonical-right-catchup-result first-world
  first-source-empty = refl
  first-source-same = refl

  second-catchup = worldRightCatchupResult second-world
  second-indexed = rightCatchupIndexedResult second-catchup
  second = weakIndexedResult second-indexed
  second-lineage = worldRightCatchupStoreLineage second-world
  second-source-empty = rightCatchupSourceChangesEmpty second-catchup
  second-source-same = rightCatchupSourceUnchanged second-catchup

  combined =
    source-silent-resultᵀ first first-source-empty first-source-same second

  combined-unique =
    worldRightCatchupAssumptionMembershipUnique second-world

  combined-type-eq =
    assumption-membership-unique→precision-index-unique
      combined-unique
      (subst
        (λ T → resultCtx combined ∣ resultLeftCtx combined
          ⊢ applyTys (sourceChanges combined) _
            ⊑ T ⊣ resultRightCtx combined)
        (targetTypeResult combined)
        (subst
          (λ S → resultCtx combined ∣ resultLeftCtx combined
            ⊢ S ⊑ resultTargetType combined
              ⊣ resultRightCtx combined)
          (sourceTypeResult combined)
          (resultType combined)))
      (transportType combined _)

  combined-transport =
    source-silent-preserves-transportᵀ first first-source-empty
      first-source-same second
      (weak-one-step-reindex-preserves-transportᵀ
        first-raw refl refl first-related
        (weakIndexedTransport first-indexed))
      (weakIndexedTransport second-indexed)

  combined-coherence =
    source-silent-preserves-type-coherenceᵀ first first-source-empty
      first-source-same second
      (weak-one-step-reindex-preserves-type-coherenceᵀ
        first-raw refl refl first-related
        (weakIndexedTypeCoherence first-indexed))
      (weakIndexedTypeCoherence second-indexed)

  combined-indexed =
    weak-one-step-index-resultᵀ
      combined combined-type-eq combined-transport combined-coherence

  combined-source-empty =
    source-silent-preserves-changes-exactᵀ first first-source-empty
      first-source-same second second-source-empty

  combined-source-same =
    trans
      (source-silent-preserves-result-exactᵀ first first-source-empty
        first-source-same second second-source-same)
      first-source-same

  combined-bullet =
    source-silent-source-bullet-transport
      first first-source-empty first-source-same second
      second-source-empty
      (worldRightCatchupSourceBulletTransport first-world)
      (worldRightCatchupSourceBulletTransport second-world)

  combined-context =
    trans second-context
      (trans
        (cong
          (applyRightImpCtxChanges
            (targetTailChanges second))
          first-context)
        (sym
          (applyRightImpCtxChanges-++
            (targetTailChanges first)
            (targetTailChanges second) _)))

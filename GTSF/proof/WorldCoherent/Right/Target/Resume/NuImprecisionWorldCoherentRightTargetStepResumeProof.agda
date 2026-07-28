module
  proof.WorldCoherent.Right.Target.Resume.NuImprecisionWorldCoherentRightTargetStepResumeProof
  where

-- File Charter:
--   * Proves the flat active-target-step resumption boundary.
--   * Composes a framed inner right catch-up, one target step, and a completed
--     continuation while retaining all world, transport, coherence, lineage,
--     and source-bullet invariants.
--   * Reuses the existing weak-step and right-value catch-up carriers; it
--     introduces no result, view, outcome, postulate, hole, or bypass.

open import proof.NuCore.Relations.NuImprecisionQuotientedTyping
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (true)
open import Data.List using ([]; _∷_; _++_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym; trans)
import Relation.Binary.HeterogeneousEquality as HE

open import Imprecision using
  (NonVar; _ˣ⊑★; _ˣ⊑ˣ_; ⇑ᵢ; ⇑ᴸᵢ; ⇑ᴿᵢ)
open import ImprecisionComposition using (⌊_⌋; ∀ˢ_; νˢ-injective)
open import ImprecisionWf using
  (_∣_⊢_⊑_⊣_; _↦_; ∀ⁱ_; ν)
open import ConversionIndexCompatibility using
  (_[_↦_]ᴸ_; _[_↦_]ᴿ_; _[_↦_⊑⟨_⟩_↤_]ᴾ_)
open import NuReduction using
  ( applyTerm
  ; applyTerms
  ; applyTy
  ; applyTys
  ; bind
  ; keep
  ; _—→[_]_
  )
open import NuTermImprecision using (StoreImp)
open import NuTerms using (No•)
open import QuotientedTermImprecision using
  ( prefix-reflⁱ
  )
open import Types using (occurs; ⇑ᵗ; _⇒_; `∀)
open import proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingAlgebra using
  ( rel-store-embedding-composeⁱ
  ; rel-store-embedding-congⁱ
  )
open import
  proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingPrefixProof
  using (rel-store-embedding-prefix-invⁱ)
open import proof.Right.Core.NuImprecisionRightContextAction using
  (applyRightImpCtxChanges; applyRightImpCtxChanges-++)
open import
  proof.Right.StorePrefix.NuImprecisionRightOnlyStoreLineageCompositionLemma
  using (weak-one-step-right-only-store-lineage-compositionᵀ)
open import proof.Right.ValueCatchup.NuImprecisionRightValueCatchupResultDef using
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
open import proof.Catchup.Simulation.NuImprecisionSimulation using
  ( weak-one-step-target-cast-frame-coherenceᵀ
  ; weak-one-step-target-cast-frame-transportᵀ
  ; weak-one-step-target-cast-frameᵀ
  )
open import proof.Catchup.Simulation.NuImprecisionSimulationCore using
  ( nu-term-imprecision-transport-termsᵀ
  ; nu-term-imprecision-transport-typesᵀ
  ; subst²-to-≅
  ; transportAllType-to-raw≅
  ; transportArrowType-to-raw≅
  ; weak-one-step-compose-all-body
  ; weak-one-step-compose-all-componentsᵀ
  ; weak-one-step-compose-arrow-componentsᵀ
  ; weak-one-step-compose-right-body
  ; weak-one-step-compose-source-nu
  ; weak-one-step-compose-preserves-type-coherenceᵀ
  ; weak-one-step-compose-preserves-transportᵀ
  ; weak-one-step-compose-type
  ; weak-one-step-compose-type-to-nested≅
  ; weak-one-step-composeᵀ
  ; weak-one-step-index-resultᵀ
  ; weak-one-step-nested-all-coherent≅
  ; weak-one-step-nested-arrow-coherent≅
  )
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  (store-imp-prefix-transⁱ)
open import proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef
open import
  proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageProof
  using (weak-one-step-compose-store-lineageᵀ)
open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightCatchupResultDef
open import
  proof.WorldCoherent.Right.Target.Resume.NuImprecisionWorldCoherentRightTargetStepResumeDef
  using (WorldCoherentRightTargetStepResumeᵀ)
open import
  proof.WorldCoherent.Right.Target.Resume.NuImprecisionWorldCoherentRightTargetStepResumeContextDef
  using (WorldCoherentRightTargetStepResumeContextᵀ)
open import proof.Core.Properties.ReductionProperties using
  ( applyTerm-preserves-No•
  ; applyTerms-++
  ; applyTerms-preserves-No•
  ; applyTyUnderTyBinder
  ; applyTy-∀
  ; applyTyVar
  ; applyTyVars
  ; applyTyVars-++
  ; applyTys-++
  ; applyTys-∀
  ; applyTysUnderTyBinders
  ; applyTysUnderTyBinders-⇑ᵗ
  ; applyTysUnderTyBinders-++
  )


open import proof.Core.Properties.NuCastImprecisionShapeProperties using
  ( shape-lift∀ᵢ
  ; shape-source-liftνᵢ
  ; shape-subst-source
  ; shape-subst-target
  ; shape-target-lift-rightᵢ
  )
open import
  proof.Core.Properties.ConversionIndexCompatibilityProperties
  using
  ( replace-left-source-shape
  ; replace-left-target-shape
  ; replace-left-transport-endpoints
  ; replace-paired-evidence-shape
  ; replace-paired-source-shape
  ; replace-paired-target-shape
  ; replace-paired-transport-endpoints
  ; replace-right-source-shape
  ; replace-right-target-shape
  ; replace-right-transport-endpoints
  ; shape-transport-imprecision-endpoints
  ; transport-imprecision-endpoints
  )
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using
  (⊑-lift∀ᵢ; ⊑-source-liftνᵢ; ⊑-target-lift-rightᵢ)
open import proof.Core.Properties.TypeProperties using
  (renameᵗ-ext-suc-comm)


private
  compose-source-bullet-transport :
    ∀ {Φ Δᴸ Δᴿ M M′ A B}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      (first : WeakOneStepResult ρ M M′ A B keep)
      {N′}
      (target→ : targetResult first —→[ keep ] N′)
      (second : WeakOneStepResult
        (resultStore first) (sourceResult first) N′
        (resultSourceType first) (resultTargetType first) keep) →
    sourceChanges first ≡ [] →
    sourceChanges second ≡ [] →
    RightValueCatchupSourceBulletTransportᵀ first →
    RightValueCatchupSourceBulletTransportᵀ second →
    RightValueCatchupSourceBulletTransportᵀ
      (weak-one-step-composeᵀ first target→ second)
  compose-source-bullet-transport
      first target→ second refl refl first-bullet second-bullet
      {L = L} {M′ = M′} {C = C} {C′ = C′} {q = q}
      prefix okL noM′ L⊢ L⊑M′ =
    nu-term-imprecision-transport-termsᵀ
      refl
      (sym (applyTerms-++
        (targetTailChanges first)
        (keep ∷ targetTailChanges second)
        (applyTerm keep M′)))
      (nu-term-imprecision-transport-typesᵀ
        (sym (applyTys-++ [] [] C))
        (sym (applyTys-++
          (targetTailChanges first)
          (keep ∷ targetTailChanges second)
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
          (targetTailChanges first)
          (applyTerm-preserves-No• keep noM′))
        (nu-term-imprecision-source-typing first-relation)
        first-relation


world-coherent-right-target-step-resume-proofᵀ :
  WorldCoherentRightTargetStepResumeᵀ
world-coherent-right-target-step-resume-proofᵀ
    {C = C} {c = c} {q = q}
    inner-world@(world-coherent-right-value-indexed-catchup
      first-catchup first-lineage first-bullet first-world
      first-exclusive first-unique first-wfR)
    framed target-step
    (world-coherent-right-value-indexed-catchup
      second-catchup second-lineage second-bullet second-world
      second-exclusive second-unique second-wfR) =
  world-coherent-right-value-indexed-catchup
    (right-value-indexed-catchup
      (weak-indexed-result combined combined-canonical
        combined-transport combined-coherence)
      source-empty source-unchanged
      (rightCatchupSourceValue first-catchup)
      (rightCatchupSourceNoBullet first-catchup)
      (rightCatchupTargetValue second-catchup)
      (rightCatchupTargetNoBullet second-catchup))
    combined-lineage combined-bullet second-world
    second-exclusive second-unique second-wfR
  where
  first-indexed = rightCatchupIndexedResult first-catchup
  first-result = weakIndexedResult first-indexed
  second-indexed = rightCatchupIndexedResult second-catchup
  second-result = weakIndexedResult second-indexed

  first =
    weak-one-step-target-cast-frameᵀ
      {B′ = C} {c = c} {χ = keep} {q = q}
      first-result framed

  combined =
    weak-one-step-composeᵀ first target-step second-result

  combined-canonical =
    nu-term-imprecision-transport-typesᵀ
      (sym (applyTys-++
        (sourceChanges first)
        (sourceChanges second-result) _))
      (sym (applyTys-++
        (targetTailChanges first)
        (keep ∷ targetTailChanges second-result) _))
      refl
      (canonicalIndexedResults second-indexed)

  source-empty : sourceChanges combined ≡ []
  source-empty =
    cong₂ _++_
      (rightCatchupSourceChangesEmpty first-catchup)
      (rightCatchupSourceChangesEmpty second-catchup)

  source-unchanged : sourceResult combined ≡ _
  source-unchanged =
    HE.≅-to-≡
      (HE.trans
        (HE.≡-to-≅ (rightCatchupSourceUnchanged second-catchup))
        (HE.≡-to-≅ (rightCatchupSourceUnchanged first-catchup)))

  first-transport =
    weak-one-step-target-cast-frame-transportᵀ
      first-result framed
      (weakIndexedTransport (rightCatchupIndexedResult first-catchup))

  first-coherence =
    weak-one-step-target-cast-frame-coherenceᵀ
      first-result framed
      (weakIndexedTypeCoherence (rightCatchupIndexedResult first-catchup))

  combined-transport =
    weak-one-step-compose-preserves-transportᵀ
      first target-step second-result first-transport
      (weakIndexedTransport (rightCatchupIndexedResult second-catchup))

  combined-coherence =
    weak-one-step-compose-preserves-type-coherenceᵀ
      first target-step second-result first-coherence
      (weakIndexedTypeCoherence (rightCatchupIndexedResult second-catchup))

  framed-lineage : WeakOneStepStoreLineage first
  framed-lineage =
    weak-step-store-lineage
      (lineageStore first-lineage)
      (lineageEmbedding first-lineage)
      (lineagePrefix first-lineage)

  combined-lineage =
    weak-one-step-compose-store-lineageᵀ
      first target-step second-result framed-lineage second-lineage

  framed-bullet : RightValueCatchupSourceBulletTransportᵀ first
  framed-bullet = first-bullet

  combined-bullet =
    compose-source-bullet-transport
      first target-step second-result
      (rightCatchupSourceChangesEmpty first-catchup)
      (rightCatchupSourceChangesEmpty second-catchup)
      framed-bullet second-bullet


world-coherent-right-target-step-resume-context-proofᵀ :
  WorldCoherentRightTargetStepResumeContextᵀ
world-coherent-right-target-step-resume-context-proofᵀ
    {Φ = Φ} {C = C} {c = c} {q = q}
    inner-world@(world-coherent-right-value-indexed-catchup
      first-catchup first-lineage first-bullet first-world
      first-exclusive first-unique first-wfR)
    first-context first-prefix framed target-step
    (world-coherent-right-value-indexed-catchup
      second-catchup second-lineage second-bullet second-world
      second-exclusive second-unique second-wfR)
    second-context second-prefix
    with weak-one-step-right-only-store-lineage-compositionᵀ
      (weak-one-step-target-cast-frameᵀ
        {B′ = C} {c = c} {χ = keep} {q = q}
        (weakIndexedResult
          (rightCatchupIndexedResult first-catchup))
        framed)
      target-step
      (weakIndexedResult
        (rightCatchupIndexedResult second-catchup))
      (weak-step-store-lineage
        (lineageStore first-lineage)
        (lineageEmbedding first-lineage)
        (lineagePrefix first-lineage))
      second-lineage first-prefix second-prefix
world-coherent-right-target-step-resume-context-proofᵀ
    {Φ = Φ} {C = C} {c = c} {q = q}
    inner-world@(world-coherent-right-value-indexed-catchup
      first-catchup first-lineage first-bullet first-world
      first-exclusive first-unique first-wfR)
    first-context first-prefix framed target-step
    (world-coherent-right-value-indexed-catchup
      second-catchup second-lineage second-bullet second-world
      second-exclusive second-unique second-wfR)
    second-context second-prefix
    | combined-lineage , combined-prefix =
  world-coherent-right-value-indexed-catchup
      (right-value-indexed-catchup
        (weak-indexed-result combined combined-canonical
          combined-transport combined-coherence)
        source-empty source-unchanged
        (rightCatchupSourceValue first-catchup)
        (rightCatchupSourceNoBullet first-catchup)
        (rightCatchupTargetValue second-catchup)
        (rightCatchupTargetNoBullet second-catchup))
      combined-lineage combined-bullet second-world
      second-exclusive second-unique second-wfR ,
  combined-context ,
  combined-prefix
  where
  first-indexed = rightCatchupIndexedResult first-catchup
  first-result = weakIndexedResult first-indexed
  second-indexed = rightCatchupIndexedResult second-catchup
  second-result = weakIndexedResult second-indexed

  first =
    weak-one-step-target-cast-frameᵀ
      {B′ = C} {c = c} {χ = keep} {q = q}
      first-result framed

  combined =
    weak-one-step-composeᵀ first target-step second-result

  combined-canonical =
    nu-term-imprecision-transport-typesᵀ
      (sym (applyTys-++
        (sourceChanges first)
        (sourceChanges second-result) _))
      (sym (applyTys-++
        (targetTailChanges first)
        (keep ∷ targetTailChanges second-result) _))
      refl
      (canonicalIndexedResults second-indexed)

  source-empty : sourceChanges combined ≡ []
  source-empty =
    cong₂ _++_
      (rightCatchupSourceChangesEmpty first-catchup)
      (rightCatchupSourceChangesEmpty second-catchup)

  source-unchanged : sourceResult combined ≡ _
  source-unchanged =
    HE.≅-to-≡
      (HE.trans
        (HE.≡-to-≅
          (rightCatchupSourceUnchanged second-catchup))
        (HE.≡-to-≅
          (rightCatchupSourceUnchanged first-catchup)))

  first-transport =
    weak-one-step-target-cast-frame-transportᵀ
      first-result framed
      (weakIndexedTransport (rightCatchupIndexedResult first-catchup))

  first-coherence =
    weak-one-step-target-cast-frame-coherenceᵀ
      first-result framed
      (weakIndexedTypeCoherence (rightCatchupIndexedResult first-catchup))

  combined-transport =
    weak-one-step-compose-preserves-transportᵀ
      first target-step second-result first-transport
      (weakIndexedTransport (rightCatchupIndexedResult second-catchup))

  combined-coherence =
    weak-one-step-compose-preserves-type-coherenceᵀ
      first target-step second-result first-coherence
      (weakIndexedTypeCoherence (rightCatchupIndexedResult second-catchup))

  framed-bullet : RightValueCatchupSourceBulletTransportᵀ first
  framed-bullet = first-bullet

  combined-bullet =
    compose-source-bullet-transport
      first target-step second-result
      (rightCatchupSourceChangesEmpty first-catchup)
      (rightCatchupSourceChangesEmpty second-catchup)
      framed-bullet second-bullet

  combined-context =
    trans second-context
      (trans
        (cong
          (applyRightImpCtxChanges
            (targetTailChanges second-result))
          first-context)
        (sym
          (applyRightImpCtxChanges-++
            (targetTailChanges first-result)
            (keep ∷ targetTailChanges second-result)
            Φ)))

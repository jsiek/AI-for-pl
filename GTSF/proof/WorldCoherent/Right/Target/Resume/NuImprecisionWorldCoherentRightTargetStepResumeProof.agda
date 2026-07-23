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

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_; _++_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; sym; trans)
import Relation.Binary.HeterogeneousEquality as HE

open import Imprecision using (_ˣ⊑ˣ_; ⇑ᵢ)
open import ImprecisionWf using
  (_∣_⊢_⊑_⊣_; _↦_; ∀ⁱ_)
open import NuReduction using
  ( applyTerm
  ; applyTerms
  ; applyTy
  ; applyTys
  ; keep
  ; _—→[_]_
  )
open import NuTermImprecision using (StoreImp)
open import NuTerms using (No•)
open import QuotientedTermImprecision using
  ( prefix-reflⁱ
  ; nu-term-imprecision-source-typing
  )
open import Types using (_⇒_; `∀)
open import proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingAlgebra using
  ( rel-store-embedding-composeⁱ
  ; rel-store-embedding-congⁱ
  ; rel-store-embedding-prefix-invⁱ
  )
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
  ; applyTyVars-++
  ; applyTys-++
  ; applyTysUnderTyBinders-++
  )


private
  weak-one-step-compose-store-lineageᵀ :
    ∀ {Φ Δᴸ Δᴿ M M′ A B χ}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      (first : WeakOneStepResult ρ M M′ A B χ)
      {χ′ N′}
      (target→ : targetResult first —→[ χ′ ] N′)
      (second : WeakOneStepResult
        (resultStore first) (sourceResult first) N′
        (resultSourceType first) (resultTargetType first) χ′) →
    WeakOneStepStoreLineage first →
    WeakOneStepStoreLineage second →
    WeakOneStepStoreLineage
      (weak-one-step-composeᵀ first target→ second)
  weak-one-step-compose-store-lineageᵀ
      first target→ second
      (weak-step-store-lineage store₁ embedding₁ prefix₁)
      (weak-step-store-lineage store₂ embedding₂ prefix₂)
      with rel-store-embedding-prefix-invⁱ prefix₁ embedding₂
  weak-one-step-compose-store-lineageᵀ
      {χ = χ} first {χ′ = χ′} target→ second
      (weak-step-store-lineage store₁ embedding₁ prefix₁)
      (weak-step-store-lineage store₂ embedding₂ prefix₂)
      | store₁₂ , embedding₁₂ , prefix₁₂ =
    weak-step-store-lineage store₁₂
      (rel-store-embedding-congⁱ
        (λ α → sym
          (applyTyVars-++
            (sourceChanges first) (sourceChanges second) α))
        (λ β → sym
          (applyTyVars-++
            (χ ∷ targetTailChanges first)
            (χ′ ∷ targetTailChanges second) β))
        (rel-store-embedding-composeⁱ embedding₁ embedding₁₂))
      (store-imp-prefix-transⁱ prefix₁₂ prefix₂)

  weak-one-step-compose-preserves-type-coherenceᵀ :
    ∀ {Φ Δᴸ Δᴿ M M′ A B χ}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      (first : WeakOneStepResult ρ M M′ A B χ)
      {χ′ N′}
      (target→ : targetResult first —→[ χ′ ] N′)
      (second : WeakOneStepResult
        (resultStore first) (sourceResult first) N′
        (resultSourceType first) (resultTargetType first) χ′) →
    WeakOneStepTypeCoherence first →
    WeakOneStepTypeCoherence second →
    WeakOneStepTypeCoherence
      (weak-one-step-composeᵀ first target→ second)
  weak-one-step-compose-preserves-type-coherenceᵀ
      {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {χ = χ}
      first {χ′ = χ′} target→ second
      first-coherence second-coherence =
    weak-step-type-coherence arrow-coherent all-coherent
    where
    combined = weak-one-step-composeᵀ first target→ second

    arrow-coherent :
      ∀ {C C′ D D′}
        (pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ)
        (pD : Φ ∣ Δᴸ ⊢ D ⊑ D′ ⊣ Δᴿ) →
      transportArrowType combined pC pD ≡
        weak-one-step-compose-type first second pC ↦
        weak-one-step-compose-type first second pD
    arrow-coherent {C = C} {C′ = C′}
        {D = D} {D′ = D′} pC pD =
      HE.≅-to-≡
        (HE.trans
          (transportArrowType-to-raw≅ combined pC pD)
          (HE.trans
            (weak-one-step-compose-type-to-nested≅
              first second (pC ↦ pD))
            (HE.trans
              (weak-one-step-nested-arrow-coherent≅
                first second first-coherence second-coherence pC pD)
              (HE.trans
                (HE.sym
                  (subst²-to-≅
                    {P = λ S T →
                      resultCtx second ∣ resultLeftCtx second
                        ⊢ S ⊑ T ⊣ resultRightCtx second}
                    (cong₂ _⇒_
                      (sym (applyTys-++
                        (sourceChanges first)
                        (sourceChanges second) C))
                      (sym (applyTys-++
                        (sourceChanges first)
                        (sourceChanges second) D)))
                    (cong₂ _⇒_
                      (sym (applyTys-++
                        (targetTailChanges first)
                        (χ′ ∷ targetTailChanges second)
                        (applyTy χ C′)))
                      (sym (applyTys-++
                        (targetTailChanges first)
                        (χ′ ∷ targetTailChanges second)
                        (applyTy χ D′))))
                    (transportType second (transportType first pC) ↦
                      transportType second (transportType first pD))))
                (HE.≡-to-≅
                  (weak-one-step-compose-arrow-componentsᵀ
                    first second pC pD))))))

    all-coherent :
      ∀ {C C′}
        (q : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
          ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ) →
      transportAllType combined q ≡
        ∀ⁱ (weak-one-step-compose-all-body first second q)
    all-coherent {C = C} {C′ = C′} q =
      HE.≅-to-≡
        (HE.trans
          (transportAllType-to-raw≅ combined q)
          (HE.trans
            (weak-one-step-compose-type-to-nested≅
              first second (∀ⁱ q))
            (HE.trans
              (weak-one-step-nested-all-coherent≅
                first second first-coherence second-coherence q)
              (HE.trans
                (HE.sym
                  (subst²-to-≅
                    {P = λ S T →
                      resultCtx second ∣ resultLeftCtx second
                        ⊢ S ⊑ T ⊣ resultRightCtx second}
                    (cong `∀
                      (sym (applyTysUnderTyBinders-++
                        (sourceChanges first)
                        (sourceChanges second) C)))
                    (cong `∀
                      (sym (applyTysUnderTyBinders-++
                        (targetTailChanges first)
                        (χ′ ∷ targetTailChanges second)
                        (applyTyUnderTyBinder χ C′))))
                    (∀ⁱ (transportAllBody second
                      (transportAllBody first q)))))
                (HE.≡-to-≅
                  (weak-one-step-compose-all-componentsᵀ
                    first second q))))))

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
      first-result framed (weakIndexedTransport (rightCatchupIndexedResult first-catchup))

  first-coherence =
    weak-one-step-target-cast-frame-coherenceᵀ
      first-result framed (weakIndexedTypeCoherence (rightCatchupIndexedResult first-catchup))

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
      first-result framed (weakIndexedTransport (rightCatchupIndexedResult first-catchup))

  first-coherence =
    weak-one-step-target-cast-frame-coherenceᵀ
      first-result framed (weakIndexedTypeCoherence (rightCatchupIndexedResult first-catchup))

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

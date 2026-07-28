module
  proof.WorldCoherent.Right.Target.Resume.NuImprecisionWorldCoherentRightTargetSequenceResumeProof
  where

-- File Charter:
--   * Proves direct target-sequence resumption after a completed shared inner
--     catch-up.
--   * Composes the framed inner target trace, the administrative sequence
--     step, and the already completed continuation without another result
--     or outcome layer.
--   * Preserves generic transport, type coherence, relational-store lineage,
--     world invariants, the source-bullet transport invariant, and the
--     contextual target-only lineage refinement.
--   * Contains no postulate, hole, permissive option, or termination bypass.

open import proof.NuCore.Relations.NuImprecisionQuotientedTyping
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (true)
open import Data.List using ([]; _∷_; _++_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_,_; Σ)
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym; trans)
import Relation.Binary.HeterogeneousEquality as HE

open import Coercions using (Coercion; _︔_)
open import ConversionIndexCompatibility
open import Imprecision using (NonVar; ⇑ᴿᵢ)
open import ImprecisionWf using
  (_ˣ⊑★; _ˣ⊑ˣ_; ⇑ᵢ; ⇑ᴸᵢ; _∣_⊢_⊑_⊣_;
   _↦_; ∀ⁱ_; ν)
open import ImprecisionComposition using (⌊_⌋; ∀ˢ_; νˢ-injective)
open import NuReduction using
  ( applyStore
  ; applyStores
  ; applyTerm
  ; applyTerms
  ; applyTy
  ; applyTyCtx
  ; applyTyCtxs
  ; applyTys
  ; keep
  ; pure-step
  )
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using
  (No•; RuntimeOK; Term; Value; _⟨_⟩)
open import QuotientedTermImprecision using
  ( prefix-reflⁱ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Types using (Ty; occurs; ⇑ᵗ; _⇒_; `∀)
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using
  (∀ᵢᶜ; ⊑-lift∀ᵢ; ⊑-source-liftνᵢ; ⊑-target-lift-rightᵢ)
open import proof.Right.Core.NuImprecisionRightContextAction using
  (applyRightImpCtxChanges; applyRightImpCtxChanges-++)
open import proof.Right.StorePrefix.NuImprecisionRightOnlyStorePrefix using
  (RightOnlyStoreImpPrefix; right-only-store-prefix)
open import proof.Right.StorePrefix.NuImprecisionRightOnlyStorePrefixAlgebra
  using
  ( rel-store-embedding-right-only-prefix-invⁱ
  ; right-only-store-prefix-transⁱ
  )
open import proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingAlgebra using
  ( rel-store-embedding-composeⁱ
  ; rel-store-embedding-congⁱ
  )
open import
  proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingPrefixProof
  using (rel-store-embedding-prefix-invⁱ)
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
open import proof.Catchup.Simulation.NuImprecisionSimulationCore using
  ( ≡-to-≅
  ; nu-term-imprecision-transport-termsᵀ
  ; nu-term-imprecision-transport-typesᵀ
  ; subst-to-≅
  ; subst²-to-≅
  ; transport-all-⊑ᵢ
  ; transport-arrow-⊑ᵢ
  ; transportAllType-to-raw≅
  ; transportArrowType-to-raw≅
  ; transportSourceNuType-to-raw≅
  ; transportType-source-subst-to-raw≅
  ; transportType-target-subst-to-raw≅
  )
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  (store-imp-prefix-transⁱ)
open import proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef
open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightCatchupResultDef
open import
  proof.WorldCoherent.Right.Target.Resume.NuImprecisionWorldCoherentRightTargetSequenceResumeDef
  using (WorldCoherentRightTargetSequenceResumeᵀ)
open import
  proof.WorldCoherent.Right.Target.Resume.NuImprecisionWorldCoherentRightTargetSequenceResumeContextDef
  using (WorldCoherentRightTargetSequenceResumeContextᵀ)
open import proof.Core.Properties.ReductionProperties using
  ( applyCoercions
  ; applyStores-++
  ; applyTerms-++
  ; applyTerms-preserves-No•
  ; applyTyCtxs-++
  ; applyTy-∀
  ; applyTyVars
  ; applyTys-++
  ; applyTys-⇒
  ; applyTys-∀
  ; applyTysUnderTyBinders
  ; applyTysUnderTyBinders-++
  ; applyTysUnderTyBinders-⇑ᵗ
  ; applyTyVars-++
  ; cast-↠
  ; ↠-trans
  )
open import proof.Core.Properties.NuCastImprecisionShapeProperties using
  ( shape-lift∀ᵢ
  ; shape-source-liftνᵢ
  ; shape-subst-source
  ; shape-subst-target
  ; shape-target-lift-rightᵢ
  )
open import proof.Core.Properties.ConversionIndexCompatibilityProperties using
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


private
  apply-coercions-sequence :
    ∀ χs s t →
    applyCoercions χs (s ︔ t) ≡
      applyCoercions χs s ︔ applyCoercions χs t
  apply-coercions-sequence [] s t = refl
  apply-coercions-sequence (keep ∷ χs) s t =
    apply-coercions-sequence χs s t
  apply-coercions-sequence (NuReduction.bind A ∷ χs) s t =
    apply-coercions-sequence χs
      (Coercions.⇑ᶜ s) (Coercions.⇑ᶜ t)

  post-catchup-sequence-step :
    ∀ χs {V s t} →
    Value V →
    V ⟨ applyCoercions χs (s ︔ t) ⟩ NuReduction.—→[ keep ]
      V ⟨ applyCoercions χs s ⟩
        ⟨ applyCoercions χs t ⟩
  post-catchup-sequence-step χs {s = s} {t = t} vV
      rewrite apply-coercions-sequence χs s t =
    pure-step (NuReduction.β-seq vV)

  sequence-resume-type :
    ∀ {Φ Δᴸ Δᴿ V M′ A B}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      (first : WeakOneStepResult ρ V M′ A B keep)
      {N′ C}
      (second : WeakOneStepResult
        (resultStore first) (sourceResult first) N′
        (applyTys (sourceChanges first) A)
        (applyTys (targetTailChanges first) C) keep)
      {D E} →
    Φ ∣ Δᴸ ⊢ D ⊑ E ⊣ Δᴿ →
    resultCtx second ∣ resultLeftCtx second
      ⊢ applyTys
          (sourceChanges first ++ sourceChanges second) D
        ⊑ applyTys
          (targetTailChanges first ++
            keep ∷ targetTailChanges second) E
        ⊣ resultRightCtx second
  sequence-resume-type first second {D = D} {E = E} p =
    subst
      (λ T → resultCtx second ∣ resultLeftCtx second
        ⊢ applyTys
            (sourceChanges first ++ sourceChanges second) D
          ⊑ T ⊣ resultRightCtx second)
      (sym (applyTys-++
        (targetTailChanges first)
        (keep ∷ targetTailChanges second) E))
      (subst
        (λ S → resultCtx second ∣ resultLeftCtx second
          ⊢ S ⊑ applyTys (targetTailChanges second)
              (applyTys (targetTailChanges first) E)
            ⊣ resultRightCtx second)
        (sym (applyTys-++
          (sourceChanges first) (sourceChanges second) D))
        (transportType second (transportType first p)))

  sequence-resume-type-to-nested≅ :
    ∀ {Φ Δᴸ Δᴿ V M′ A B}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      (first : WeakOneStepResult ρ V M′ A B keep)
      {N′ C}
      (second : WeakOneStepResult
        (resultStore first) (sourceResult first) N′
        (applyTys (sourceChanges first) A)
        (applyTys (targetTailChanges first) C) keep)
      {D E}
      (p : Φ ∣ Δᴸ ⊢ D ⊑ E ⊣ Δᴿ) →
    HE._≅_ (sequence-resume-type first second p)
      (transportType second (transportType first p))
  sequence-resume-type-to-nested≅ first second
      {D = D} {E = E} p =
    HE.trans
      (subst-to-≅ target-eq source-transport)
      (subst-to-≅ source-eq raw)
    where
    raw = transportType second (transportType first p)
    source-eq = sym (applyTys-++
      (sourceChanges first) (sourceChanges second) D)
    source-transport = subst
      (λ S → resultCtx second ∣ resultLeftCtx second
        ⊢ S ⊑ applyTys (targetTailChanges second)
            (applyTys (targetTailChanges first) E)
          ⊣ resultRightCtx second)
      source-eq raw
    target-eq = sym (applyTys-++
      (targetTailChanges first)
      (keep ∷ targetTailChanges second) E)

  sequence-nested-source-nu≅ :
    ∀ {Φ Δᴸ Δᴿ V M′ A B}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      (first : WeakOneStepResult ρ V M′ A B keep)
      {N′ X Y}
      (second : WeakOneStepResult
        (resultStore first) (sourceResult first) N′ X Y keep)
      {C D}
      (safe : NonVar C)
      (occ : occurs zero C ≡ true)
      (q : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        ∣ suc Δᴸ ⊢ C ⊑ D ⊣ Δᴿ) →
    let first-shape = transportSourceNu first safe occ q in
    let second-shape = transportSourceNu second
          (sourceNuSafe first-shape)
          (sourceNuOccurs first-shape)
          (sourceNuBody first-shape) in
    HE._≅_
      (transportType second (transportType first (ν safe occ q)))
      (transportSourceNuType second
        (sourceNuSafe first-shape)
        (sourceNuOccurs first-shape)
        (sourceNuBody first-shape))
  sequence-nested-source-nu≅ first second safe occ q =
    HE.trans
      (HE.sym
        (transportType-source-subst-to-raw≅ second
          (applyTys-∀ (sourceChanges first) _)
          (transportType first (ν safe occ q))))
      (HE.trans
        (≡-to-≅
          (cong (transportType second)
            (sourceNuIndexEquality first-shape)))
        (HE.sym
          (transportSourceNuType-to-raw≅ second
            (sourceNuSafe first-shape)
            (sourceNuOccurs first-shape)
            (sourceNuBody first-shape))))
    where
    first-shape = transportSourceNu first safe occ q

  sequence-resume-source-nu :
    ∀ {Φ Δᴸ Δᴿ V M′ A B}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      (first : WeakOneStepResult ρ V M′ A B keep)
      {N′ C}
      (second : WeakOneStepResult
        (resultStore first) (sourceResult first) N′
        (applyTys (sourceChanges first) A)
        (applyTys (targetTailChanges first) C) keep)
      {D E}
      (safe : NonVar D)
      (occ : occurs zero D ≡ true)
      (q : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        ∣ suc Δᴸ ⊢ D ⊑ E ⊣ Δᴿ) →
    SourceNuIndex
      (subst
        (λ S → resultCtx second ∣ resultLeftCtx second
          ⊢ S ⊑ applyTys
              (targetTailChanges first ++
                keep ∷ targetTailChanges second) E
            ⊣ resultRightCtx second)
        (applyTys-∀
          (sourceChanges first ++ sourceChanges second) D)
        (sequence-resume-type first second (ν safe occ q)))
  sequence-resume-source-nu first second {D = D} {E = E}
      safe occ q =
    sourceNuIndex-reindex (sym combined-eq) transported-shape
    where
    first-shape = transportSourceNu first safe occ q

    second-shape = transportSourceNu second
      (sourceNuSafe first-shape)
      (sourceNuOccurs first-shape)
      (sourceNuBody first-shape)

    source-eq = applyTysUnderTyBinders-++
      (sourceChanges first) (sourceChanges second) D

    target-eq = applyTys-++
      (targetTailChanges first)
      (keep ∷ targetTailChanges second) E

    transported-shape =
      sourceNuIndex-transport
        (sym source-eq) (sym target-eq) second-shape

    combined-eq =
      HE.≅-to-≡
        (HE.trans
          (subst-to-≅
            {P = λ S → resultCtx second ∣ resultLeftCtx second
              ⊢ S ⊑
                  applyTys
                    (targetTailChanges first ++
                      keep ∷ targetTailChanges second) E
                ⊣ resultRightCtx second}
            (applyTys-∀
              (sourceChanges first ++ sourceChanges second) D)
            (sequence-resume-type
              first second (ν safe occ q)))
          (HE.trans
            (sequence-resume-type-to-nested≅
              first second (ν safe occ q))
            (HE.trans
              (sequence-nested-source-nu≅
                first second safe occ q)
              (HE.sym
                (subst²-to-≅
                  {P = λ S T → resultCtx second
                    ∣ resultLeftCtx second
                    ⊢ S ⊑ T ⊣ resultRightCtx second}
                  (cong `∀ (sym source-eq)) (sym target-eq)
                  (transportSourceNuType second
                    (sourceNuSafe first-shape)
                    (sourceNuOccurs first-shape)
                    (sourceNuBody first-shape)))))))

  sequence-resume-all-body :
    ∀ {Φ Δᴸ Δᴿ V M′ A B}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      (first : WeakOneStepResult ρ V M′ A B keep)
      {N′ C}
      (second : WeakOneStepResult
        (resultStore first) (sourceResult first) N′
        (applyTys (sourceChanges first) A)
        (applyTys (targetTailChanges first) C) keep)
      {D E} →
    ∀ᵢᶜ Φ ∣ _ ⊢ D ⊑ E ⊣ _ →
    ∀ᵢᶜ (resultCtx second) ∣ _
      ⊢ applyTysUnderTyBinders
          (sourceChanges first ++ sourceChanges second) D
        ⊑ applyTysUnderTyBinders
          (targetTailChanges first ++
            keep ∷ targetTailChanges second) E
        ⊣ _
  sequence-resume-all-body first second {D = D} {E = E} p =
    subst
      (λ T → ∀ᵢᶜ (resultCtx second) ∣ _
        ⊢ applyTysUnderTyBinders
            (sourceChanges first ++ sourceChanges second) D
          ⊑ T ⊣ _)
      (sym (applyTysUnderTyBinders-++
        (targetTailChanges first)
        (keep ∷ targetTailChanges second) E))
      (subst
        (λ S → ∀ᵢᶜ (resultCtx second) ∣ _
          ⊢ S ⊑ applyTysUnderTyBinders
              (targetTailChanges second)
              (applyTysUnderTyBinders
                (targetTailChanges first) E)
            ⊣ _)
        (sym (applyTysUnderTyBinders-++
          (sourceChanges first) (sourceChanges second) D))
        (transportAllBody second (transportAllBody first p)))

  sequence-resume-right-body :
    ∀ {Φ Δᴸ Δᴿ V M′ A B}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      (first : WeakOneStepResult ρ V M′ A B keep)
      {N′ C}
      (second : WeakOneStepResult
        (resultStore first) (sourceResult first) N′
        (applyTys (sourceChanges first) A)
        (applyTys (targetTailChanges first) C) keep)
      {D E} →
    ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ D ⊑ E ⊣ suc Δᴿ →
    ⇑ᴿᵢ (resultCtx second) ∣ resultLeftCtx second
      ⊢ applyTys
          (sourceChanges first ++ sourceChanges second) D
        ⊑ applyTysUnderTyBinders
          (targetTailChanges first ++
            keep ∷ targetTailChanges second) E
        ⊣ suc (resultRightCtx second)
  sequence-resume-right-body first second {D = D} {E = E} p =
    subst
      (λ T → ⇑ᴿᵢ (resultCtx second) ∣ resultLeftCtx second
        ⊢ applyTys
            (sourceChanges first ++ sourceChanges second) D
          ⊑ T ⊣ suc (resultRightCtx second))
      (sym (applyTysUnderTyBinders-++
        (targetTailChanges first)
        (keep ∷ targetTailChanges second) E))
      (subst
        (λ S → ⇑ᴿᵢ (resultCtx second) ∣ resultLeftCtx second
          ⊢ S ⊑ applyTysUnderTyBinders
              (targetTailChanges second)
              (applyTysUnderTyBinders
                (targetTailChanges first) E)
            ⊣ suc (resultRightCtx second))
        (sym (applyTys-++
          (sourceChanges first) (sourceChanges second) D))
        (transportRightBody second (transportRightBody first p)))

  sequence-resume-result :
    ∀ {Φ Δᴸ Δᴿ V M′ A B}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      (first : WeakOneStepResult ρ V M′ A B keep)
      {C s t}
      (second : WeakOneStepResult
        (resultStore first) (sourceResult first)
        ((targetResult first
          ⟨ applyCoercions (targetTailChanges first) s ⟩)
          ⟨ applyCoercions (targetTailChanges first) t ⟩)
        (applyTys (sourceChanges first) A)
        (applyTys (targetTailChanges first) C) keep) →
    Value (targetResult first) →
    WeakOneStepResult ρ V (M′ ⟨ s ︔ t ⟩) A C keep
  sequence-resume-result
      {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {ρ = ρ}
      first {C = C} {s = s} {t = t} second vW =
    record
      { sourceChanges =
          sourceChanges first ++ sourceChanges second
      ; targetTailChanges =
          targetTailChanges first ++
            keep ∷ targetTailChanges second
      ; sourceResult = sourceResult second
      ; targetResult = targetResult second
      ; resultCtx = resultCtx second
      ; resultLeftCtx = resultLeftCtx second
      ; resultRightCtx = resultRightCtx second
      ; sourceCtxResult =
          trans (sourceCtxResult second)
            (trans
              (cong (applyTyCtxs (sourceChanges second))
                (sourceCtxResult first))
              (sym (applyTyCtxs-++
                (sourceChanges first) (sourceChanges second) Δᴸ)))
      ; targetCtxResult =
          trans (targetCtxResult second)
            (trans
              (cong (applyTyCtxs (targetTailChanges second))
                (targetCtxResult first))
              (sym (applyTyCtxs-++
                (targetTailChanges first)
                (keep ∷ targetTailChanges second) Δᴿ)))
      ; resultStore = resultStore second
      ; resultSourceType = resultSourceType second
      ; resultTargetType = resultTargetType second
      ; sourceTypeResult =
          trans (sourceTypeResult second)
            (sym (applyTys-++
              (sourceChanges first) (sourceChanges second) _))
      ; targetTypeResult =
          trans (targetTypeResult second)
            (sym (applyTys-++
              (targetTailChanges first)
              (keep ∷ targetTailChanges second) C))
      ; transportType = sequence-resume-type first second
      ; transportAllBody = sequence-resume-all-body first second
      ; transportRightBody = sequence-resume-right-body first second
      ; transportSourceNu = sequence-resume-source-nu first second
      ; resultType = resultType second
      ; sourceCatchup =
          ↠-trans (sourceCatchup first) (sourceCatchup second)
      ; targetTail =
          ↠-trans (cast-↠ (targetTail first))
            (NuReduction.↠-step
              (post-catchup-sequence-step
                (targetTailChanges first) vW)
              (targetTail second))
      ; sourceStoreResult =
          trans (sourceStoreResult second)
            (trans
              (cong (applyStores (sourceChanges second))
                (sourceStoreResult first))
              (sym (applyStores-++
                (sourceChanges first) (sourceChanges second)
                (leftStoreⁱ ρ))))
      ; targetStoreResult =
          trans (targetStoreResult second)
            (trans
              (cong (applyStores (targetTailChanges second))
                (targetStoreResult first))
              (sym (applyStores-++
                (targetTailChanges first)
                (keep ∷ targetTailChanges second)
                (rightStoreⁱ ρ))))
      ; relatedResults = relatedResults second
      }

  sequence-resume-transport-body :
    ∀ {Φ Δᴸ Δᴿ V M′ A B}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      (first : WeakOneStepResult ρ V M′ A B keep)
      {C s t}
      (second : WeakOneStepResult
        (resultStore first) (sourceResult first)
        ((targetResult first
          ⟨ applyCoercions (targetTailChanges first) s ⟩)
          ⟨ applyCoercions (targetTailChanges first) t ⟩)
        (applyTys (sourceChanges first) A)
        (applyTys (targetTailChanges first) C) keep) →
    WeakOneStepTransport first →
    WeakOneStepTransport second →
    ∀ {L L′ D E p} →
    No• L →
    No• L′ →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ L ⊑ L′ ⦂ D ⊑ E ∶ p →
    resultCtx second
      ∣ resultLeftCtx second
      ∣ resultRightCtx second
      ∣ resultStore second ∣ []
      ⊢ᴺ applyTerms
          (sourceChanges first ++ sourceChanges second) L
        ⊑ applyTerms
          (targetTailChanges first ++
            keep ∷ targetTailChanges second) L′
        ⦂ applyTys
            (sourceChanges first ++ sourceChanges second) D
          ⊑ applyTys
            (targetTailChanges first ++
              keep ∷ targetTailChanges second) E
          ∶ sequence-resume-type first second p
  sequence-resume-transport-body
      first second first-transport second-transport
      {L = L} {L′ = L′} {D = D} {E = E} {p = p}
      noL noL′ L⊑L′
      rewrite applyTerms-++
        (sourceChanges first) (sourceChanges second) L
      | applyTerms-++
        (targetTailChanges first)
        (keep ∷ targetTailChanges second) L′
      | applyTys-++
        (sourceChanges first) (sourceChanges second) D
      | applyTys-++
        (targetTailChanges first)
        (keep ∷ targetTailChanges second) E =
    transportNo•Terms second-transport
      {L = applyTerms (sourceChanges first) L}
      {L′ = applyTerms (targetTailChanges first) L′}
      {C = applyTys (sourceChanges first) D}
      {C′ = applyTys (targetTailChanges first) E}
      {p = transportType first p}
      (applyTerms-preserves-No• (sourceChanges first) noL)
      (applyTerms-preserves-No•
        (targetTailChanges first) noL′)
      (transportNo•Terms first-transport noL noL′ L⊑L′)

  sequence-resume-transport :
    ∀ {Φ Δᴸ Δᴿ V M′ A B}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      (first : WeakOneStepResult ρ V M′ A B keep)
      {C s t}
      (second : WeakOneStepResult
        (resultStore first) (sourceResult first)
        ((targetResult first
          ⟨ applyCoercions (targetTailChanges first) s ⟩)
          ⟨ applyCoercions (targetTailChanges first) t ⟩)
        (applyTys (sourceChanges first) A)
        (applyTys (targetTailChanges first) C) keep) →
    (vW : Value (targetResult first)) →
    WeakOneStepTransport first →
    WeakOneStepTransport second →
    WeakOneStepTransport
      (sequence-resume-result first second vW)
  sequence-resume-transport
      first second vW first-transport second-transport =
    weak-step-transport
      (sequence-resume-transport-body
        first second first-transport second-transport)

  sequence-transport-arrow-to-raw≅ :
    ∀ {Φ Δᴸ Δᴿ V M′ A B}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      (first : WeakOneStepResult ρ V M′ A B keep)
      {N′ X Y}
      (second : WeakOneStepResult
        (resultStore first) (sourceResult first) N′ X Y keep)
      {C C′ D D′}
      (pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ)
      (pD : Φ ∣ Δᴸ ⊢ D ⊑ D′ ⊣ Δᴿ) →
    HE._≅_
      (transportType second (transportArrowType first pC pD))
      (transportType second (transportType first (pC ↦ pD)))
  sequence-transport-arrow-to-raw≅ first second
      {C = C} {C′ = C′} {D = D} {D′ = D′} pC pD =
    HE.trans
      (transportType-target-subst-to-raw≅
        second target-eq source-transport)
      (transportType-source-subst-to-raw≅ second source-eq raw)
    where
    raw = transportType first (pC ↦ pD)
    source-eq = applyTys-⇒ (sourceChanges first) C D
    source-transport = subst
      (λ S → resultCtx first ∣ resultLeftCtx first
        ⊢ S ⊑ applyTys (targetTailChanges first) (C′ ⇒ D′)
          ⊣ resultRightCtx first)
      source-eq raw
    target-eq = applyTys-⇒ (targetTailChanges first) C′ D′

  sequence-transport-all-to-raw≅ :
    ∀ {Φ Δᴸ Δᴿ V M′ A B}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      (first : WeakOneStepResult ρ V M′ A B keep)
      {N′ X Y}
      (second : WeakOneStepResult
        (resultStore first) (sourceResult first) N′ X Y keep)
      {C C′}
      (q : ∀ᵢᶜ Φ ∣ _ ⊢ C ⊑ C′ ⊣ _) →
    HE._≅_
      (transportType second (transportAllType first q))
      (transportType second (transportType first (∀ⁱ q)))
  sequence-transport-all-to-raw≅ first second
      {C = C} {C′ = C′} q =
    HE.trans
      (transportType-target-subst-to-raw≅
        second target-eq source-transport)
      (transportType-source-subst-to-raw≅ second source-eq raw)
    where
    raw = transportType first (∀ⁱ q)
    source-eq = applyTys-∀ (sourceChanges first) C
    source-transport = subst
      (λ S → resultCtx first ∣ resultLeftCtx first
        ⊢ S ⊑ applyTys (targetTailChanges first) (`∀ C′)
          ⊣ resultRightCtx first)
      source-eq raw
    target-eq = applyTys-∀ (targetTailChanges first) C′

  sequence-nested-arrow-coherent≅ :
    ∀ {Φ Δᴸ Δᴿ V M′ A B}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      (first : WeakOneStepResult ρ V M′ A B keep)
      {N′ X Y}
      (second : WeakOneStepResult
        (resultStore first) (sourceResult first) N′ X Y keep) →
    WeakOneStepTypeCoherence first →
    WeakOneStepTypeCoherence second →
    ∀ {C C′ D D′}
      (pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ)
      (pD : Φ ∣ Δᴸ ⊢ D ⊑ D′ ⊣ Δᴿ) →
    HE._≅_
      (transportType second (transportType first (pC ↦ pD)))
      (transportType second (transportType first pC) ↦
        transportType second (transportType first pD))
  sequence-nested-arrow-coherent≅
      first second first-coherence second-coherence pC pD =
    HE.trans
      (HE.sym (sequence-transport-arrow-to-raw≅
        first second pC pD))
      (HE.trans
        (≡-to-≅
          (cong (transportType second)
            (transportArrowCoherent first-coherence pC pD)))
        (HE.trans
          (HE.sym (transportArrowType-to-raw≅ second
            (transportType first pC) (transportType first pD)))
          (≡-to-≅
            (transportArrowCoherent second-coherence
              (transportType first pC) (transportType first pD)))))

  sequence-nested-all-coherent≅ :
    ∀ {Φ Δᴸ Δᴿ V M′ A B}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      (first : WeakOneStepResult ρ V M′ A B keep)
      {N′ X Y}
      (second : WeakOneStepResult
        (resultStore first) (sourceResult first) N′ X Y keep) →
    WeakOneStepTypeCoherence first →
    WeakOneStepTypeCoherence second →
    ∀ {C C′}
      (q : ∀ᵢᶜ Φ ∣ _ ⊢ C ⊑ C′ ⊣ _) →
    HE._≅_
      (transportType second (transportType first (∀ⁱ q)))
      (∀ⁱ (transportAllBody second (transportAllBody first q)))
  sequence-nested-all-coherent≅
      first second first-coherence second-coherence q =
    HE.trans
      (HE.sym (sequence-transport-all-to-raw≅ first second q))
      (HE.trans
        (≡-to-≅
          (cong (transportType second)
            (transportAllCoherent first-coherence q)))
        (HE.trans
          (HE.sym (transportAllType-to-raw≅ second
            (transportAllBody first q)))
          (≡-to-≅
            (transportAllCoherent second-coherence
              (transportAllBody first q)))))

  sequence-resume-coherence :
    ∀ {Φ Δᴸ Δᴿ V M′ A B}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      (first : WeakOneStepResult ρ V M′ A B keep)
      {C s t}
      (second : WeakOneStepResult
        (resultStore first) (sourceResult first)
        ((targetResult first
          ⟨ applyCoercions (targetTailChanges first) s ⟩)
          ⟨ applyCoercions (targetTailChanges first) t ⟩)
        (applyTys (sourceChanges first) A)
        (applyTys (targetTailChanges first) C) keep) →
    (vW : Value (targetResult first)) →
    WeakOneStepTypeCoherence first →
    WeakOneStepTypeCoherence second →
    WeakOneStepTypeCoherence
      (sequence-resume-result first second vW)
  sequence-resume-coherence
      {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      first second vW first-coherence second-coherence =
    weak-step-type-coherence arrow-coherent all-coherent
      shape-coherent right-body-shape-coherent
      left-replacement-coherent right-replacement-coherent
      paired-replacement-coherent
      all-body-paired-replacement-coherent
      source-nu-body-left-replacement-coherent
      right-body-right-replacement-coherent
    where
    combined = sequence-resume-result first second vW

    arrow-coherent :
      ∀ {C C′ D D′}
        (pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ)
        (pD : Φ ∣ Δᴸ ⊢ D ⊑ D′ ⊣ Δᴿ) →
      transportArrowType combined pC pD ≡
        sequence-resume-type first second pC ↦
        sequence-resume-type first second pD
    arrow-coherent {C = C} {C′ = C′}
        {D = D} {D′ = D′} pC pD =
      HE.≅-to-≡
        (HE.trans
          (transportArrowType-to-raw≅ combined pC pD)
          (HE.trans
            (sequence-resume-type-to-nested≅
              first second (pC ↦ pD))
            (HE.trans
              (sequence-nested-arrow-coherent≅
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
                        (keep ∷ targetTailChanges second) C′))
                      (sym (applyTys-++
                        (targetTailChanges first)
                        (keep ∷ targetTailChanges second) D′)))
                    (transportType second (transportType first pC) ↦
                      transportType second (transportType first pD))))
                (≡-to-≅
                  (transport-arrow-⊑ᵢ
                    (sym (applyTys-++
                      (sourceChanges first)
                      (sourceChanges second) C))
                    (sym (applyTys-++
                      (targetTailChanges first)
                      (keep ∷ targetTailChanges second) C′))
                    (sym (applyTys-++
                      (sourceChanges first)
                      (sourceChanges second) D))
                    (sym (applyTys-++
                      (targetTailChanges first)
                      (keep ∷ targetTailChanges second) D′))))))))

    all-coherent :
      ∀ {C C′}
        (q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ) →
      transportAllType combined q ≡
        ∀ⁱ (sequence-resume-all-body first second q)
    all-coherent {C = C} {C′ = C′} q =
      HE.≅-to-≡
        (HE.trans
          (transportAllType-to-raw≅ combined q)
          (HE.trans
            (sequence-resume-type-to-nested≅
              first second (∀ⁱ q))
            (HE.trans
              (sequence-nested-all-coherent≅
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
                        (keep ∷ targetTailChanges second) C′)))
                    (∀ⁱ (transportAllBody second
                      (transportAllBody first q)))))
                (≡-to-≅
                  (transport-all-⊑ᵢ
                    (sym (applyTysUnderTyBinders-++
                      (sourceChanges first)
                      (sourceChanges second) C))
                    (sym (applyTysUnderTyBinders-++
                      (targetTailChanges first)
                      (keep ∷ targetTailChanges second) C′))))))))

    shape-coherent :
      ∀ {C D}
        (p : Φ ∣ Δᴸ ⊢ C ⊑ D ⊣ Δᴿ) →
      ⌊ sequence-resume-type first second p ⌋ ≡ ⌊ p ⌋
    shape-coherent {C = C} {D = D} p =
      trans
        (shape-subst-target target-eq source-transport)
        (trans
          (shape-subst-source source-eq nested)
          (trans
            (transportShapeCoherent second-coherence
              (transportType first p))
            (transportShapeCoherent first-coherence p)))
      where
      nested = transportType second (transportType first p)
      source-eq = sym
        (applyTys-++ (sourceChanges first) (sourceChanges second) C)
      source-transport =
        subst
          (λ S → resultCtx second ∣ resultLeftCtx second
            ⊢ S ⊑ applyTys (targetTailChanges second)
                (applyTys (targetTailChanges first) D)
            ⊣ resultRightCtx second)
          source-eq nested
      target-eq = sym
        (applyTys-++ (targetTailChanges first)
          (keep ∷ targetTailChanges second) D)

    composed-type-nested-shape :
      ∀ {C D}
        (p : Φ ∣ Δᴸ ⊢ C ⊑ D ⊣ Δᴿ) →
      ⌊ sequence-resume-type first second p ⌋ ≡
        ⌊ transport-imprecision-endpoints
            (sym
              (applyTys-++
                (sourceChanges first) (sourceChanges second) C))
            (sym
              (applyTys-++
                (targetTailChanges first)
                (keep ∷ targetTailChanges second) D))
            (transportType second (transportType first p))
        ⌋
    composed-type-nested-shape {C = C} {D = D} p =
      trans
        (shape-coherent p)
        (trans
          (sym (transportShapeCoherent first-coherence p))
          (trans
            (sym
              (transportShapeCoherent second-coherence
                (transportType first p)))
            (sym
              (shape-transport-imprecision-endpoints
                source-eq target-eq nested))))
      where
      nested = transportType second (transportType first p)
      source-eq = sym
        (applyTys-++ (sourceChanges first) (sourceChanges second) C)
      target-eq = sym
        (applyTys-++ (targetTailChanges first)
          (keep ∷ targetTailChanges second) D)

    right-body-shape-coherent :
      ∀ {C D}
        (p : ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ C ⊑ D ⊣ suc Δᴿ) →
      ⌊ sequence-resume-right-body first second p ⌋ ≡ ⌊ p ⌋
    right-body-shape-coherent {C = C} {D = D} p =
      trans
        (shape-subst-target target-eq source-transport)
        (trans
          (shape-subst-source source-eq nested)
          (trans
            (transportRightBodyShapeCoherent second-coherence
              (transportRightBody first p))
            (transportRightBodyShapeCoherent first-coherence p)))
      where
      nested = transportRightBody second (transportRightBody first p)
      source-eq = sym
        (applyTys-++ (sourceChanges first) (sourceChanges second) C)
      source-transport =
        subst
          (λ S → ⇑ᴿᵢ (resultCtx second) ∣ resultLeftCtx second
            ⊢ S ⊑ applyTysUnderTyBinders
                (targetTailChanges second)
                (applyTysUnderTyBinders
                  (targetTailChanges first) D)
            ⊣ suc (resultRightCtx second))
          source-eq nested
      target-eq = sym
        (applyTysUnderTyBinders-++
          (targetTailChanges first)
          (keep ∷ targetTailChanges second) D)

    left-replacement-coherent :
      ∀ {C C′ D α X}
        {p : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ D ⊑ C′ ⊣ Δᴿ} →
      p [ α ↦ X ]ᴸ q →
      sequence-resume-type first second p
        [ applyTyVars
            (sourceChanges first ++ sourceChanges second) α
        ↦ applyTys
            (sourceChanges first ++ sourceChanges second) X ]ᴸ
      sequence-resume-type first second q
    left-replacement-coherent
        {C = C} {C′ = C′} {D = D} {α = α} {X = X}
        {p = p} {q = q} replacement
      rewrite applyTyVars-++
                (sourceChanges first) (sourceChanges second) α =
      replace-left-target-shape
        (composed-type-nested-shape q)
        (replace-left-source-shape
          (composed-type-nested-shape p)
          endpoints-replacement)
      where
      second-replacement =
        transportLeftReplacementCoherent second-coherence
          (transportLeftReplacementCoherent
            first-coherence replacement)
      input-source-eq = sym
        (applyTys-++ (sourceChanges first) (sourceChanges second) C)
      target-eq = sym
        (applyTys-++ (targetTailChanges first)
          (keep ∷ targetTailChanges second) C′)
      output-source-eq = sym
        (applyTys-++ (sourceChanges first) (sourceChanges second) D)
      inserted-source-eq = sym
        (applyTys-++ (sourceChanges first) (sourceChanges second) X)
      endpoints-replacement =
        replace-left-transport-endpoints
          input-source-eq target-eq output-source-eq
          inserted-source-eq second-replacement

    right-replacement-coherent :
      ∀ {C C′ D′ β X′}
        {p : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ C ⊑ D′ ⊣ Δᴿ} →
      p [ β ↦ X′ ]ᴿ q →
      sequence-resume-type first second p
        [ applyTyVars
            (targetTailChanges first ++
              keep ∷ targetTailChanges second) β
        ↦ applyTys
            (targetTailChanges first ++
              keep ∷ targetTailChanges second) X′ ]ᴿ
      sequence-resume-type first second q
    right-replacement-coherent
        {C = C} {C′ = C′} {D′ = D′}
        {β = β} {X′ = X′} {p = p} {q = q} replacement
      rewrite applyTyVars-++
                (targetTailChanges first)
                (keep ∷ targetTailChanges second) β =
      replace-right-target-shape
        (composed-type-nested-shape q)
        (replace-right-source-shape
          (composed-type-nested-shape p)
          endpoints-replacement)
      where
      second-replacement =
        transportRightReplacementCoherent second-coherence
          (transportRightReplacementCoherent
            first-coherence replacement)
      input-source-eq = sym
        (applyTys-++ (sourceChanges first) (sourceChanges second) C)
      input-target-eq = sym
        (applyTys-++ (targetTailChanges first)
          (keep ∷ targetTailChanges second) C′)
      output-target-eq = sym
        (applyTys-++ (targetTailChanges first)
          (keep ∷ targetTailChanges second) D′)
      inserted-target-eq = sym
        (applyTys-++ (targetTailChanges first)
          (keep ∷ targetTailChanges second) X′)
      endpoints-replacement =
        replace-right-transport-endpoints
          input-source-eq input-target-eq
          output-target-eq inserted-target-eq
          second-replacement

    paired-replacement-coherent :
      ∀ {C C′ D D′ α β X X′}
        {pX : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ}
        {p : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ D ⊑ D′ ⊣ Δᴿ} →
      p [ α ↦ X ⊑⟨ pX ⟩ X′ ↤ β ]ᴾ q →
      sequence-resume-type first second p
        [ applyTyVars
            (sourceChanges first ++ sourceChanges second) α
        ↦ applyTys
            (sourceChanges first ++ sourceChanges second) X
        ⊑⟨ sequence-resume-type first second pX ⟩
        applyTys
          (targetTailChanges first ++
            keep ∷ targetTailChanges second) X′
        ↤ applyTyVars
            (targetTailChanges first ++
              keep ∷ targetTailChanges second) β ]ᴾ
      sequence-resume-type first second q
    paired-replacement-coherent
        {C = C} {C′ = C′} {D = D} {D′ = D′}
        {α = α} {β = β} {X = X} {X′ = X′}
        {pX = pX} {p = p} {q = q} replacement
      rewrite applyTyVars-++
                (sourceChanges first) (sourceChanges second) α
            | applyTyVars-++
                (targetTailChanges first)
                (keep ∷ targetTailChanges second) β =
      replace-paired-target-shape
        (composed-type-nested-shape q)
        (replace-paired-source-shape
          (composed-type-nested-shape p)
          (replace-paired-evidence-shape
            (composed-type-nested-shape pX)
            endpoints-replacement))
      where
      second-replacement =
        transportPairedReplacementCoherent second-coherence
          (transportPairedReplacementCoherent
            first-coherence replacement)
      input-source-eq = sym
        (applyTys-++ (sourceChanges first) (sourceChanges second) C)
      input-target-eq = sym
        (applyTys-++ (targetTailChanges first)
          (keep ∷ targetTailChanges second) C′)
      output-source-eq = sym
        (applyTys-++ (sourceChanges first) (sourceChanges second) D)
      output-target-eq = sym
        (applyTys-++ (targetTailChanges first)
          (keep ∷ targetTailChanges second) D′)
      inserted-source-eq = sym
        (applyTys-++ (sourceChanges first) (sourceChanges second) X)
      inserted-target-eq = sym
        (applyTys-++ (targetTailChanges first)
          (keep ∷ targetTailChanges second) X′)
      endpoints-replacement =
        replace-paired-transport-endpoints
          input-source-eq input-target-eq
          output-source-eq output-target-eq
          inserted-source-eq inserted-target-eq
          second-replacement

    ∀ˢ-injective-compose :
      ∀ {s t} →
      ∀ˢ s ≡ ∀ˢ t →
      s ≡ t
    ∀ˢ-injective-compose refl = refl

    first-all-type-raw-shape :
      ∀ {C C′}
        (q : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
          ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ) →
      ⌊ transportAllType first q ⌋ ≡
        ⌊ transportType first (∀ⁱ q) ⌋
    first-all-type-raw-shape {C = C} {C′ = C′} q =
      trans
        (shape-subst-target target-eq source-transport)
        (shape-subst-source source-eq raw)
      where
      raw = transportType first (∀ⁱ q)
      source-eq = applyTys-∀ (sourceChanges first) C
      source-transport =
        subst
          (λ S → resultCtx first ∣ resultLeftCtx first
            ⊢ S ⊑ applyTys (targetTailChanges first) (`∀ C′)
            ⊣ resultRightCtx first)
          source-eq raw
      target-eq = applyTys-∀ (targetTailChanges first) C′

    first-all-body-shape :
      ∀ {C C′}
        (q : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
          ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ) →
      ⌊ transportAllBody first q ⌋ ≡ ⌊ q ⌋
    first-all-body-shape q =
      ∀ˢ-injective-compose
        (trans
          (sym (cong ⌊_⌋
            (transportAllCoherent first-coherence q)))
          (trans
            (first-all-type-raw-shape q)
            (transportShapeCoherent first-coherence (∀ⁱ q))))

    second-all-type-raw-shape :
      ∀ {C C′}
        (q : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ (resultCtx first))
          ∣ suc (resultLeftCtx first)
          ⊢ C ⊑ C′ ⊣ suc (resultRightCtx first)) →
      ⌊ transportAllType second q ⌋ ≡
        ⌊ transportType second (∀ⁱ q) ⌋
    second-all-type-raw-shape {C = C} {C′ = C′} q =
      trans
        (shape-subst-target target-eq source-transport)
        (shape-subst-source source-eq raw)
      where
      raw = transportType second (∀ⁱ q)
      source-eq = applyTys-∀ (sourceChanges second) C
      source-transport =
        subst
          (λ S → resultCtx second ∣ resultLeftCtx second
            ⊢ S ⊑ applyTys (targetTailChanges second) (`∀ C′)
            ⊣ resultRightCtx second)
          source-eq raw
      target-eq = applyTys-∀ (targetTailChanges second) C′

    second-all-body-shape :
      ∀ {C C′}
        (q : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ (resultCtx first))
          ∣ suc (resultLeftCtx first)
          ⊢ C ⊑ C′ ⊣ suc (resultRightCtx first)) →
      ⌊ transportAllBody second q ⌋ ≡ ⌊ q ⌋
    second-all-body-shape q =
      ∀ˢ-injective-compose
        (trans
          (sym (cong ⌊_⌋
            (transportAllCoherent second-coherence q)))
          (trans
            (second-all-type-raw-shape q)
            (transportShapeCoherent second-coherence (∀ⁱ q))))

    composed-all-body-shape :
      ∀ {C C′}
        (q : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
          ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ) →
      ⌊ sequence-resume-all-body first second q ⌋ ≡ ⌊ q ⌋
    composed-all-body-shape {C = C} {C′ = C′} q =
      trans
        (shape-subst-target target-eq source-transport)
        (trans
          (shape-subst-source source-eq nested)
          (trans
            (second-all-body-shape (transportAllBody first q))
            (first-all-body-shape q)))
      where
      nested = transportAllBody second (transportAllBody first q)
      source-eq = sym
        (applyTysUnderTyBinders-++
          (sourceChanges first) (sourceChanges second) C)
      source-transport =
        subst
          (λ S → ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ (resultCtx second))
            ∣ suc (resultLeftCtx second)
            ⊢ S ⊑ applyTysUnderTyBinders
                (targetTailChanges second)
                (applyTysUnderTyBinders
                  (targetTailChanges first) C′)
            ⊣ suc (resultRightCtx second))
          source-eq nested
      target-eq = sym
        (applyTysUnderTyBinders-++
          (targetTailChanges first)
          (keep ∷ targetTailChanges second) C′)

    all-body-paired-replacement-coherent :
      ∀ {A₀ A′ B B′ C C′}
        {A⇑⊑A′⇑ :
          ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
            ∣ suc Δᴸ ⊢ ⇑ᵗ A₀ ⊑ ⇑ᵗ A′ ⊣ suc Δᴿ}
        {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
        {q : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
          ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ} →
      q
        [ zero ↦ ⇑ᵗ A₀
        ⊑⟨ A⇑⊑A′⇑ ⟩
        ⇑ᵗ A′ ↤ zero ]ᴾ
      ⊑-lift∀ᵢ pB →
      sequence-resume-all-body first second q
        [ zero ↦
            applyTysUnderTyBinders
              (sourceChanges first ++ sourceChanges second)
              (⇑ᵗ A₀)
        ⊑⟨ sequence-resume-all-body first second A⇑⊑A′⇑ ⟩
        applyTysUnderTyBinders
          (targetTailChanges first ++
            keep ∷ targetTailChanges second)
          (⇑ᵗ A′)
        ↤ zero ]ᴾ
      ⊑-lift∀ᵢ (sequence-resume-type first second pB)
    all-body-paired-replacement-coherent
        {A₀ = A₀} {A′ = A′} {B = B} {B′ = B′}
        {C = C} {C′ = C′}
        {A⇑⊑A′⇑ = A⇑⊑A′⇑} {pB = pB} {q = q}
        replacement =
      replace-paired-target-shape target-shape
        (replace-paired-source-shape source-shape
          (replace-paired-evidence-shape evidence-shape
            endpoints-replacement))
      where
      first-replacement =
        transportAllBodyPairedReplacementCoherent
          first-coherence replacement

      source-shift =
        applyTysUnderTyBinders-⇑ᵗ (sourceChanges first) A₀

      target-shift =
        applyTysUnderTyBinders-⇑ᵗ (targetTailChanges first) A′

      normalized-first-replacement =
        replace-paired-transport-endpoints
          refl refl refl refl source-shift target-shift
          first-replacement

      second-replacement =
        transportAllBodyPairedReplacementCoherent
          second-coherence normalized-first-replacement

      input-source-eq = sym
        (applyTysUnderTyBinders-++
          (sourceChanges first) (sourceChanges second) C)

      input-target-eq = sym
        (applyTysUnderTyBinders-++
          (targetTailChanges first)
          (keep ∷ targetTailChanges second) C′)

      output-source-eq = cong ⇑ᵗ
        (sym
          (applyTys-++
            (sourceChanges first) (sourceChanges second) B))

      output-target-eq = cong ⇑ᵗ
        (sym
          (applyTys-++
            (targetTailChanges first)
            (keep ∷ targetTailChanges second) B′))

      inserted-source-eq =
        trans
          (sym
            (cong
              (applyTysUnderTyBinders (sourceChanges second))
              source-shift))
          (sym
            (applyTysUnderTyBinders-++
              (sourceChanges first) (sourceChanges second)
              (⇑ᵗ A₀)))

      inserted-target-eq =
        trans
          (sym
            (cong
              (applyTysUnderTyBinders
                (keep ∷ targetTailChanges second))
              target-shift))
          (sym
            (applyTysUnderTyBinders-++
              (targetTailChanges first)
              (keep ∷ targetTailChanges second)
              (⇑ᵗ A′)))

      endpoints-replacement =
        replace-paired-transport-endpoints
          input-source-eq input-target-eq
          output-source-eq output-target-eq
          inserted-source-eq inserted-target-eq
          second-replacement

      raw-input =
        transportAllBody second (transportAllBody first q)

      source-shape =
        trans
          (composed-all-body-shape q)
          (trans
            (sym (first-all-body-shape q))
            (trans
              (sym
                (second-all-body-shape
                  (transportAllBody first q)))
              (sym
                (shape-transport-imprecision-endpoints
                  input-source-eq input-target-eq raw-input))))

      nested-output = transportType second (transportType first pB)

      raw-output = ⊑-lift∀ᵢ nested-output

      target-shape =
        trans
          (shape-lift∀ᵢ
            (sequence-resume-type first second pB))
          (trans
            (shape-coherent pB)
            (trans
              (sym (transportShapeCoherent first-coherence pB))
              (trans
                (sym
                  (transportShapeCoherent second-coherence
                    (transportType first pB)))
                (trans
                  (sym (shape-lift∀ᵢ nested-output))
                  (sym
                    (shape-transport-imprecision-endpoints
                      output-source-eq output-target-eq
                      raw-output))))))

      normalized-inserted =
        transport-imprecision-endpoints source-shift target-shift
          (transportAllBody first A⇑⊑A′⇑)

      second-inserted =
        transportAllBody second normalized-inserted

      evidence-shape =
        trans
          (composed-all-body-shape A⇑⊑A′⇑)
          (trans
            (sym (first-all-body-shape A⇑⊑A′⇑))
            (trans
              (sym
                (shape-transport-imprecision-endpoints
                  source-shift target-shift
                  (transportAllBody first A⇑⊑A′⇑)))
              (trans
                (sym (second-all-body-shape normalized-inserted))
                (sym
                  (shape-transport-imprecision-endpoints
                    inserted-source-eq inserted-target-eq
                    second-inserted)))))

    first-source-nu-body-shape :
      ∀ {C D}
        (safe : NonVar C)
        (occ : occurs zero C ≡ true)
        (q : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
          ∣ suc Δᴸ ⊢ C ⊑ D ⊣ Δᴿ) →
      ⌊ sourceNuBody (transportSourceNu first safe occ q) ⌋
        ≡ ⌊ q ⌋
    first-source-nu-body-shape {C = C} safe occ q =
      νˢ-injective
        (trans
          (sym (cong ⌊_⌋ (sourceNuIndexEquality final-index)))
          (trans
            (shape-subst-source
              (applyTys-∀ (sourceChanges first) C)
              (transportType first (ν safe occ q)))
            (transportShapeCoherent
              first-coherence (ν safe occ q))))
      where
      final-index = transportSourceNu first safe occ q

    second-source-nu-body-shape :
      ∀ {C D}
        (safe : NonVar C)
        (occ : occurs zero C ≡ true)
        (q : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ (resultCtx first))
          ∣ suc (resultLeftCtx first)
          ⊢ C ⊑ D ⊣ resultRightCtx first) →
      ⌊ sourceNuBody (transportSourceNu second safe occ q) ⌋
        ≡ ⌊ q ⌋
    second-source-nu-body-shape {C = C} safe occ q =
      νˢ-injective
        (trans
          (sym (cong ⌊_⌋ (sourceNuIndexEquality final-index)))
          (trans
            (shape-subst-source
              (applyTys-∀ (sourceChanges second) C)
              (transportType second (ν safe occ q)))
            (transportShapeCoherent
              second-coherence (ν safe occ q))))
      where
      final-index = transportSourceNu second safe occ q

    composed-source-nu-body-shape :
      ∀ {C D}
        (safe : NonVar C)
        (occ : occurs zero C ≡ true)
        (q : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
          ∣ suc Δᴸ ⊢ C ⊑ D ⊣ Δᴿ) →
      ⌊ sourceNuBody
          (sequence-resume-source-nu
            first second safe occ q) ⌋
        ≡ ⌊ q ⌋
    composed-source-nu-body-shape {C = C} safe occ q =
      νˢ-injective
        (trans
          (sym (cong ⌊_⌋ (sourceNuIndexEquality final-index)))
          (trans
            (shape-subst-source
              (applyTys-∀
                (sourceChanges first ++ sourceChanges second) C)
              (sequence-resume-type
                first second (ν safe occ q)))
            (shape-coherent (ν safe occ q))))
      where
      final-index =
        sequence-resume-source-nu first second safe occ q

    source-nu-body-left-replacement-coherent :
      ∀ {A₀ B B′ C}
        {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
        {q : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
          ∣ suc Δᴸ ⊢ C ⊑ B′ ⊣ Δᴿ}
        (safe : NonVar C)
        (occ : occurs zero C ≡ true) →
      q [ zero ↦ ⇑ᵗ A₀ ]ᴸ ⊑-source-liftνᵢ pB →
      sourceNuBody
          (sequence-resume-source-nu
            first second safe occ q)
        [ zero ↦
            applyTysUnderTyBinders
              (sourceChanges first ++ sourceChanges second)
              (⇑ᵗ A₀) ]ᴸ
      ⊑-source-liftνᵢ
        (sequence-resume-type first second pB)
    source-nu-body-left-replacement-coherent
        {A₀ = A₀} {B = B} {B′ = B′} {C = C}
        {pB = pB} {q = q} safe occ replacement =
      replace-left-target-shape target-shape
        (replace-left-source-shape source-shape
          endpoints-replacement)
      where
      first-index = transportSourceNu first safe occ q

      first-replacement =
        transportSourceNuBodyLeftReplacementCoherent
          first-coherence safe occ replacement

      source-shift =
        applyTysUnderTyBinders-⇑ᵗ (sourceChanges first) A₀

      normalized-first-replacement =
        replace-left-transport-endpoints
          refl refl refl source-shift first-replacement

      second-index =
        transportSourceNu second
          (sourceNuSafe first-index)
          (sourceNuOccurs first-index)
          (sourceNuBody first-index)

      second-replacement =
        transportSourceNuBodyLeftReplacementCoherent
          second-coherence
          (sourceNuSafe first-index)
          (sourceNuOccurs first-index)
          normalized-first-replacement

      input-source-eq = sym
        (applyTysUnderTyBinders-++
          (sourceChanges first) (sourceChanges second) C)

      target-eq = sym
        (applyTys-++
          (targetTailChanges first)
          (keep ∷ targetTailChanges second) B′)

      output-source-eq = cong ⇑ᵗ
        (sym
          (applyTys-++
            (sourceChanges first) (sourceChanges second) B))

      inserted-source-eq =
        trans
          (sym
            (cong
              (applyTysUnderTyBinders (sourceChanges second))
              source-shift))
          (sym
            (applyTysUnderTyBinders-++
              (sourceChanges first) (sourceChanges second)
              (⇑ᵗ A₀)))

      endpoints-replacement =
        replace-left-transport-endpoints
          input-source-eq target-eq
          output-source-eq inserted-source-eq
          second-replacement

      raw-input = sourceNuBody second-index

      source-shape =
        trans
          (composed-source-nu-body-shape safe occ q)
          (trans
            (sym (first-source-nu-body-shape safe occ q))
            (trans
              (sym
                (second-source-nu-body-shape
                  (sourceNuSafe first-index)
                  (sourceNuOccurs first-index)
                  (sourceNuBody first-index)))
              (sym
                (shape-transport-imprecision-endpoints
                  input-source-eq target-eq raw-input))))

      nested-output = transportType second (transportType first pB)

      raw-output = ⊑-source-liftνᵢ nested-output

      target-shape =
        trans
          (shape-source-liftνᵢ
            (sequence-resume-type first second pB))
          (trans
            (shape-coherent pB)
            (trans
              (sym (transportShapeCoherent first-coherence pB))
              (trans
                (sym
                  (transportShapeCoherent second-coherence
                    (transportType first pB)))
                (trans
                  (sym (shape-source-liftνᵢ nested-output))
                  (sym
                    (shape-transport-imprecision-endpoints
                      output-source-eq target-eq raw-output))))))

    right-body-right-replacement-coherent :
      ∀ {A₀ B B′ C′}
        {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
        {pC : ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ B ⊑ C′ ⊣ suc Δᴿ} →
      pC [ zero ↦ ⇑ᵗ A₀ ]ᴿ ⊑-target-lift-rightᵢ pB →
      sequence-resume-right-body first second pC
        [ zero ↦
            applyTysUnderTyBinders
              (targetTailChanges first ++
                keep ∷ targetTailChanges second)
              (⇑ᵗ A₀) ]ᴿ
      ⊑-target-lift-rightᵢ
        (sequence-resume-type first second pB)
    right-body-right-replacement-coherent
        {A₀ = A₀} {B = B} {B′ = B′} {C′ = C′}
        {pB = pB} {pC = pC} replacement =
      replace-right-target-shape target-shape
        (replace-right-source-shape source-shape
          endpoints-replacement)
      where
      first-replacement =
        transportRightBodyRightReplacementCoherent
          first-coherence replacement

      target-shift =
        applyTysUnderTyBinders-⇑ᵗ
          (targetTailChanges first) A₀

      normalized-first-replacement =
        replace-right-transport-endpoints
          refl refl refl target-shift first-replacement

      second-replacement =
        transportRightBodyRightReplacementCoherent
          second-coherence normalized-first-replacement

      input-source-eq = sym
        (applyTys-++
          (sourceChanges first) (sourceChanges second) B)

      input-target-eq = sym
        (applyTysUnderTyBinders-++
          (targetTailChanges first)
          (keep ∷ targetTailChanges second) C′)

      output-target-eq = cong ⇑ᵗ
        (sym
          (applyTys-++
            (targetTailChanges first)
            (keep ∷ targetTailChanges second) B′))

      inserted-target-eq =
        trans
          (sym
            (cong
              (applyTysUnderTyBinders
                (keep ∷ targetTailChanges second))
              target-shift))
          (sym
            (applyTysUnderTyBinders-++
              (targetTailChanges first)
              (keep ∷ targetTailChanges second)
              (⇑ᵗ A₀)))

      endpoints-replacement =
        replace-right-transport-endpoints
          input-source-eq input-target-eq
          output-target-eq inserted-target-eq
          second-replacement

      raw-input =
        transportRightBody second (transportRightBody first pC)

      source-shape =
        trans
          (right-body-shape-coherent pC)
          (trans
            (sym
              (transportRightBodyShapeCoherent first-coherence pC))
            (trans
              (sym
                (transportRightBodyShapeCoherent second-coherence
                  (transportRightBody first pC)))
              (sym
                (shape-transport-imprecision-endpoints
                  input-source-eq input-target-eq raw-input))))

      nested-output = transportType second (transportType first pB)

      raw-output = ⊑-target-lift-rightᵢ nested-output

      target-shape =
        trans
          (shape-target-lift-rightᵢ
            (sequence-resume-type first second pB))
          (trans
            (shape-coherent pB)
            (trans
              (sym (transportShapeCoherent first-coherence pB))
              (trans
                (sym
                  (transportShapeCoherent second-coherence
                    (transportType first pB)))
                (trans
                  (sym (shape-target-lift-rightᵢ nested-output))
                  (sym
                    (shape-transport-imprecision-endpoints
                      input-source-eq output-target-eq
                      raw-output))))))

  sequence-resume-store-lineage :
    ∀ {Φ Δᴸ Δᴿ V M′ A B}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      (first : WeakOneStepResult ρ V M′ A B keep)
      {C s t}
      (second : WeakOneStepResult
        (resultStore first) (sourceResult first)
        ((targetResult first
          ⟨ applyCoercions (targetTailChanges first) s ⟩)
          ⟨ applyCoercions (targetTailChanges first) t ⟩)
        (applyTys (sourceChanges first) A)
        (applyTys (targetTailChanges first) C) keep) →
    (vW : Value (targetResult first)) →
    WeakOneStepStoreLineage first →
    WeakOneStepStoreLineage second →
    WeakOneStepStoreLineage
      (sequence-resume-result first second vW)
  sequence-resume-store-lineage
      first second vW
      (weak-step-store-lineage store₁ embedding₁ prefix₁)
      (weak-step-store-lineage store₂ embedding₂ prefix₂)
      with rel-store-embedding-prefix-invⁱ prefix₁ embedding₂
  sequence-resume-store-lineage
      first second vW
      (weak-step-store-lineage store₁ embedding₁ prefix₁)
      (weak-step-store-lineage store₂ embedding₂ prefix₂)
      | store₁₂ , embedding₁₂ , prefix₁₂ =
    weak-step-store-lineage store₁₂
      (rel-store-embedding-congⁱ
        (λ α → sym
          (applyTyVars-++
            (sourceChanges first)
            (sourceChanges second) α))
        (λ β → sym
          (applyTyVars-++
            (targetTailChanges first)
            (keep ∷ targetTailChanges second) β))
        (rel-store-embedding-composeⁱ embedding₁ embedding₁₂))
      (store-imp-prefix-transⁱ prefix₁₂ prefix₂)

  sequence-resume-right-only-store-lineage :
    ∀ {Φ Δᴸ Δᴿ V M′ A B}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      (first : WeakOneStepResult ρ V M′ A B keep)
      {C s t}
      (second : WeakOneStepResult
        (resultStore first) (sourceResult first)
        ((targetResult first
          ⟨ applyCoercions (targetTailChanges first) s ⟩)
          ⟨ applyCoercions (targetTailChanges first) t ⟩)
        (applyTys (sourceChanges first) A)
        (applyTys (targetTailChanges first) C) keep) →
    (vW : Value (targetResult first)) →
    (first-lineage : WeakOneStepStoreLineage first) →
    (second-lineage : WeakOneStepStoreLineage second) →
    RightOnlyStoreImpPrefix
      (lineageStore first-lineage) (resultStore first) →
    RightOnlyStoreImpPrefix
      (lineageStore second-lineage) (resultStore second) →
    Σ
      (WeakOneStepStoreLineage
        (sequence-resume-result first second vW))
      (λ lineage →
        RightOnlyStoreImpPrefix
          (lineageStore lineage)
          (resultStore
            (sequence-resume-result first second vW)))
  sequence-resume-right-only-store-lineage
      first second vW
      (weak-step-store-lineage store₁ embedding₁ prefix₁)
      (weak-step-store-lineage store₂ embedding₂ prefix₂)
      first-prefix second-prefix
      with rel-store-embedding-right-only-prefix-invⁱ
        first-prefix embedding₂
  sequence-resume-right-only-store-lineage
      first second vW
      (weak-step-store-lineage store₁ embedding₁ prefix₁)
      (weak-step-store-lineage store₂ embedding₂ prefix₂)
      first-prefix second-prefix
      | store₁₂ , embedding₁₂ , prefix₁₂ =
    weak-step-store-lineage store₁₂
        (rel-store-embedding-congⁱ
          (λ α → sym
            (applyTyVars-++
              (sourceChanges first)
              (sourceChanges second) α))
          (λ β → sym
            (applyTyVars-++
              (targetTailChanges first)
              (keep ∷ targetTailChanges second) β))
          (rel-store-embedding-composeⁱ embedding₁ embedding₁₂))
        (right-only-store-prefix combined-prefix) ,
      combined-prefix
    where
    combined-prefix =
      right-only-store-prefix-transⁱ prefix₁₂ second-prefix

  sequence-resume-source-bullet-transport :
    ∀ {Φ Δᴸ Δᴿ V M′ A B}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      (first : WeakOneStepResult ρ V M′ A B keep)
      {C s t}
      (second : WeakOneStepResult
        (resultStore first) (sourceResult first)
        ((targetResult first
          ⟨ applyCoercions (targetTailChanges first) s ⟩)
          ⟨ applyCoercions (targetTailChanges first) t ⟩)
        (applyTys (sourceChanges first) A)
        (applyTys (targetTailChanges first) C) keep) →
    (vW : Value (targetResult first)) →
    sourceChanges first ≡ [] →
    sourceChanges second ≡ [] →
    RightValueCatchupSourceBulletTransportᵀ first →
    RightValueCatchupSourceBulletTransportᵀ second →
    RightValueCatchupSourceBulletTransportᵀ
      (sequence-resume-result first second vW)
  sequence-resume-source-bullet-transport
      first second vW refl refl first-bullet second-bullet
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
          (targetTailChanges first) noM′)
        (nu-term-imprecision-source-typing first-relation)
        first-relation


world-coherent-right-target-sequence-resume-proofᵀ :
  WorldCoherentRightTargetSequenceResumeᵀ
world-coherent-right-target-sequence-resume-proofᵀ
    {C = C} {q = q}
    (world-coherent-right-value-indexed-catchup
      (right-value-indexed-catchup
        (weak-indexed-result first first-canonical
          first-transport first-coherence)
        refl refl vV noV vW noW)
      first-lineage first-bullet first-world
      first-exclusive first-unique first-wfR)
    (world-coherent-right-value-indexed-catchup
      (right-value-indexed-catchup
        (weak-indexed-result second second-canonical
          second-transport second-coherence)
        refl refl vV₂ noV₂ vZ noZ)
      second-lineage second-bullet second-world
      second-exclusive second-unique second-wfR) =
  world-coherent-right-value-indexed-catchup
    (right-value-indexed-catchup
      (weak-indexed-result combined combined-canonical
        combined-transport combined-coherence)
      refl refl vV noV vZ noZ)
    combined-lineage combined-bullet second-world
    second-exclusive second-unique second-wfR
  where
  combined = sequence-resume-result first second vW

  combined-canonical =
    nu-term-imprecision-transport-typesᵀ
      (sym (applyTys-++ [] [] _))
      (sym (applyTys-++
        (targetTailChanges first)
        (keep ∷ targetTailChanges second)
        (applyTy keep C)))
      refl
      second-canonical

  combined-transport =
    sequence-resume-transport
      first second vW first-transport second-transport

  combined-coherence =
    sequence-resume-coherence
      first second vW first-coherence second-coherence

  combined-lineage =
    sequence-resume-store-lineage
      first second vW first-lineage second-lineage

  combined-bullet =
    sequence-resume-source-bullet-transport
      first second vW refl refl first-bullet second-bullet


world-coherent-right-target-sequence-resume-context-proofᵀ :
  WorldCoherentRightTargetSequenceResumeContextᵀ
world-coherent-right-target-sequence-resume-context-proofᵀ
    {Φ = Φ} {C = C} {q = q}
    (world-coherent-right-value-indexed-catchup
      (right-value-indexed-catchup
        (weak-indexed-result first first-canonical
          first-transport first-coherence)
        refl refl vV noV vW noW)
      first-lineage first-bullet first-world
      first-exclusive first-unique first-wfR)
    first-context first-prefix
    (world-coherent-right-value-indexed-catchup
      (right-value-indexed-catchup
        (weak-indexed-result second second-canonical
          second-transport second-coherence)
        refl refl vV₂ noV₂ vZ noZ)
      second-lineage second-bullet second-world
      second-exclusive second-unique second-wfR)
    second-context second-prefix
    with sequence-resume-right-only-store-lineage
      first second vW first-lineage second-lineage
      first-prefix second-prefix
world-coherent-right-target-sequence-resume-context-proofᵀ
    {Φ = Φ} {C = C} {q = q}
    (world-coherent-right-value-indexed-catchup
      (right-value-indexed-catchup
        (weak-indexed-result first first-canonical
          first-transport first-coherence)
        refl refl vV noV vW noW)
      first-lineage first-bullet first-world
      first-exclusive first-unique first-wfR)
    first-context first-prefix
    (world-coherent-right-value-indexed-catchup
      (right-value-indexed-catchup
        (weak-indexed-result second second-canonical
          second-transport second-coherence)
        refl refl vV₂ noV₂ vZ noZ)
      second-lineage second-bullet second-world
      second-exclusive second-unique second-wfR)
    second-context second-prefix
    | combined-lineage , combined-prefix =
  world-coherent-right-value-indexed-catchup
      (right-value-indexed-catchup
        (weak-indexed-result combined combined-canonical
          combined-transport combined-coherence)
        refl refl vV noV vZ noZ)
      combined-lineage combined-bullet second-world
      second-exclusive second-unique second-wfR ,
    combined-context ,
    combined-prefix
  where
  combined = sequence-resume-result first second vW

  combined-canonical =
    nu-term-imprecision-transport-typesᵀ
      (sym (applyTys-++ [] [] _))
      (sym (applyTys-++
        (targetTailChanges first)
        (keep ∷ targetTailChanges second)
        (applyTy keep C)))
      refl
      second-canonical

  combined-transport =
    sequence-resume-transport
      first second vW first-transport second-transport

  combined-coherence =
    sequence-resume-coherence
      first second vW first-coherence second-coherence

  combined-bullet =
    sequence-resume-source-bullet-transport
      first second vW refl refl first-bullet second-bullet

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
            (keep ∷ targetTailChanges second)
            Φ)))

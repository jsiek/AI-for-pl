module
  proof.NuImprecisionWorldCoherentRightTargetSequenceResumeProof
  where

-- File Charter:
--   * Proves direct target-sequence resumption after a completed shared inner
--     catch-up.
--   * Composes the framed inner target trace, the administrative sequence
--     step, and the already completed continuation without another result
--     or outcome layer.
--   * Preserves generic transport, type coherence, relational-store lineage,
--     world invariants, and the source-bullet transport invariant.
--   * Contains no postulate, hole, permissive option, or termination bypass.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_; _++_)
open import Data.Nat using (suc)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym; trans)
import Relation.Binary.HeterogeneousEquality as HE

open import Coercions using (Coercion; _︔_)
open import Imprecision using (⇑ᴿᵢ)
open import ImprecisionWf using
  (_∣_⊢_⊑_⊣_; _↦_; ∀ⁱ_)
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
open import NuTermImprecision using
  (StoreImp; leftStoreⁱ; rightStoreⁱ)
open import NuTerms using
  (No•; RuntimeOK; Term; Value; _⟨_⟩)
open import QuotientedTermImprecision using
  ( prefix-reflⁱ
  ; nu-term-imprecision-source-typing
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Types using (Ty; _⇒_; `∀)
open import proof.LeftChangeNarrowingSeparated using
  (applyTys-⇒)
open import proof.MaximalLowerBoundsWf using (∀ᵢᶜ)
open import proof.NuImprecisionRelStoreEmbeddingAlgebra using
  ( rel-store-embedding-composeⁱ
  ; rel-store-embedding-congⁱ
  ; rel-store-embedding-prefix-invⁱ
  )
open import proof.NuImprecisionRightValueCatchupResultDef using
  ( right-value-indexed-catchup
  ; rightCatchupIndexedResult
  ; rightCatchupSourceChangesEmpty
  ; rightCatchupSourceNoBullet
  ; rightCatchupSourceUnchanged
  ; rightCatchupSourceValue
  ; rightCatchupTargetNoBullet
  ; rightCatchupTargetValue
  ; rightCatchupTransport
  ; rightCatchupTypeCoherence
  )
open import
  proof.NuImprecisionRightValueCatchupSourceBulletTransportDef
  using (RightValueCatchupSourceBulletTransportᵀ)
open import proof.NuImprecisionSimulationCore using
  ( ≡-to-≅
  ; nu-term-imprecision-transport-termsᵀ
  ; nu-term-imprecision-transport-typesᵀ
  ; subst-to-≅
  ; subst²-to-≅
  ; transport-all-⊑ᵢ
  ; transport-arrow-⊑ᵢ
  ; transportAllType-to-raw≅
  ; transportArrowType-to-raw≅
  ; transportType-source-subst-to-raw≅
  ; transportType-target-subst-to-raw≅
  )
open import proof.NuImprecisionSimulationResultDef
open import proof.NuImprecisionStorePrefix using
  (store-imp-prefix-transⁱ)
open import proof.NuImprecisionWeakOneStepStoreLineageDef
open import
  proof.NuImprecisionWorldCoherentRightCatchupResultDef
open import
  proof.NuImprecisionWorldCoherentRightTargetSequenceResumeDef
  using (WorldCoherentRightTargetSequenceResumeᵀ)
open import proof.ReductionProperties using
  ( applyCoercions
  ; applyStores-++
  ; applyTerms-++
  ; applyTerms-preserves-No•
  ; applyTyCtxs-++
  ; applyTy-∀
  ; applyTys-++
  ; applyTys-∀
  ; applyTysUnderTyBinders
  ; applyTysUnderTyBinders-++
  ; applyTyVars-++
  ; cast-↠
  ; ↠-trans
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
        (weak-indexed-result first first-canonical)
        refl refl vV noV vW noW first-transport first-coherence)
      first-lineage first-bullet first-world
      first-exclusive first-unique first-wfR)
    (world-coherent-right-value-indexed-catchup
      (right-value-indexed-catchup
        (weak-indexed-result second second-canonical)
        refl refl vV₂ noV₂ vZ noZ second-transport second-coherence)
      second-lineage second-bullet second-world
      second-exclusive second-unique second-wfR) =
  world-coherent-right-value-indexed-catchup
    (right-value-indexed-catchup
      (weak-indexed-result combined combined-canonical)
      refl refl vV noV vZ noZ combined-transport combined-coherence)
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

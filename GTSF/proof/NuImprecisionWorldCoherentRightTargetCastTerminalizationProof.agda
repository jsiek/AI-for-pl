module
  proof.NuImprecisionWorldCoherentRightTargetCastTerminalizationProof
  where

-- File Charter:
--   * Assembles the five target-only cast-terminalization entries by
--     dispatching hereditary target-administration plans.
--   * Delegates inert, pending-sequence, and active-root work only to their
--     flat constructor-specific capabilities.
--   * Uses the direct sequence-resume proof to splice smaller-rank nested
--     target continuations back under their original sequence casts.
--   * Contains no result, outcome, view, alias, postulate, hole, permissive
--     option, compatibility wrapper, or termination bypass.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import Coercions as C
open import Coercions using
  (Coercion; ModeEnv; id-onlyᵈ; _︔_)
open import Conversion using
  ( ConcealConversion
  ; RevealConversion
  ; conceal-all
  ; conceal-fun
  ; conceal-id-base
  ; conceal-id-var
  ; conceal-id-★
  ; conceal-seal
  ; reveal-all
  ; reveal-fun
  ; reveal-id-base
  ; reveal-id-var
  ; reveal-id-★
  ; reveal-unseal
  )
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import NarrowWiden using
  ( Narrowing
  ; StrictNarrowing
  ; StrictWidening
  ; Widening
  ; narrow-weaken
  ; strictⁿ→narrow
  ; strictʷ→widen
  ; widen-weaken
  ; _∣_∣_⊢_∶_⊒_
  ; _∣_∣_⊢_∶_⊑_
  )
import NarrowWiden as NW
open import NuReduction using
  ( applyStores
  ; applyTyCtxs
  ; applyTys
  ; keep
  )
open import NuStore using (StoreWf)
open import NuTermImprecision using
  (StoreImp; rightStoreⁱ)
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; Term
  ; Value
  ; no•-⟨⟩
  ; ok-no
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; prefix-reflⁱ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Store using (StoreIncl)
open import TermTyping using
  (CastMode; SealModeStore★)
open import Types using (Ty; TyCtx)
open import proof.CoercionProperties using (modeRename-id-only)
open import proof.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuImprecisionSimulationCore using
  (apply-narrows-typing; seal★-id-only)
open import proof.NuImprecisionStorePrefix using
  (rightStoreⁱ-prefix-inclusion)
open import proof.NuImprecisionTargetAdministrationMeasureProof using
  (target-sequence-rank-decreases)
open import proof.NuImprecisionTargetAdministrationPlanDef using
  ( TargetAdministrationPlan
  ; plan-id
  ; plan-inert
  ; plan-inst
  ; plan-seq
  ; plan-unseal
  ; plan-untag
  )
open import proof.NuImprecisionTargetAdministrationPlanSynthesisDef using
  ( targetNarrowingAdministrationPlan
  ; targetWideningAdministrationPlan
  )
open import proof.NuImprecisionTargetAdministrationPlanSynthesisLemma using
  (target-administration-plan-synthesisᵀ)
open import proof.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.NuImprecisionRightValueCatchupResultDef using
  ( right-value-indexed-catchup
  ; rightCatchupIndexedResult
  ; rightCatchupSourceNoBullet
  ; rightCatchupSourceValue
  ; rightCatchupTargetNoBullet
  ; rightCatchupTargetValue
  )
open import proof.NuImprecisionSimulationResultDef using
  ( WeakOneStepResult
  ; canonicalIndexedResults
  ; resultRightCtx
  ; resultStore
  ; targetCtxResult
  ; targetStoreResult
  ; targetTailChanges
  ; transportType
  ; weakIndexedResult
  )
open import
  proof.NuImprecisionWorldCoherentRightCatchupResultDef
  using
  ( WorldCoherentRightValueCatchupIndexedResult
  ; world-coherent-right-value-indexed-catchup
  ; worldRightCatchupCoherence
  ; worldRightCatchupResult
  ; worldRightCatchupSourceNameExclusive
  ; worldRightCatchupTargetStoreWf
  )
open import
  proof.NuImprecisionWorldCoherentRightTargetActiveRootResumeDef
open import
  proof.NuImprecisionWorldCoherentRightTargetAllocationFramesDef
  using (WorldCoherentRightTargetAllocationFrames)
open import
  proof.NuImprecisionWorldCoherentRightTargetCastTerminalizationDef
  using (WorldCoherentRightTargetCastTerminalization)
open import
  proof.NuImprecisionWorldCoherentRightTargetInertFramingDef
  using (WorldCoherentRightTargetInertFramingᵀ)
open import
  proof.NuImprecisionWorldCoherentRightTargetPendingSequenceContinuationDef
open import
  proof.NuImprecisionWorldCoherentRightTargetSequenceResumeProof
  using (world-coherent-right-target-sequence-resume-proofᵀ)
open import proof.NuWideningTransport using
  (apply-fixed-widens-typing; apply-widens-typing)
open import proof.ReductionProperties using
  ( applyCoercions
  ; applyCoercions-preserves-Inert
  )
open import proof.TypePreservation using (seal★-weaken)


private
  split-narrowing-sequence :
    ∀ {s t} → Narrowing (s ︔ t) → Narrowing s × Narrowing t
  split-narrowing-sequence (gG NW.？︔ gⁿ) =
    NW.untag gG , strictⁿ→narrow (NW.strict-crossⁿ gⁿ)
  split-narrowing-sequence (sⁿ NW.︔seal α) =
    strictⁿ→narrow sⁿ , NW.sealⁿ _ α

  split-widening-sequence :
    ∀ {s t} → Widening (s ︔ t) → Widening s × Widening t
  split-widening-sequence (sʷ NW.︔ gG !) =
    strictʷ→widen (NW.strict-crossʷ sʷ) , NW.tag gG
  split-widening-sequence (NW.unseal︔_ α tʷ) =
    NW.unsealʷ α _ , strictʷ→widen tʷ

  apply-coercions-sequence :
    ∀ χs s t →
    applyCoercions χs (s ︔ t) ≡
      applyCoercions χs s ︔ applyCoercions χs t
  apply-coercions-sequence [] s t = refl
  apply-coercions-sequence (keep ∷ χs) s t =
    apply-coercions-sequence χs s t
  apply-coercions-sequence (NuReduction.bind A ∷ χs) s t =
    apply-coercions-sequence χs (C.⇑ᶜ s) (C.⇑ᶜ t)

  final-narrow-sequence :
    ∀ {Φ Δᴸ Δᴿ V M′ A B}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      (result : WeakOneStepResult ρ V M′ A B keep)
      {μ C D s t} →
    μ ∣ applyTyCtxs (targetTailChanges result) Δᴿ
      ∣ applyStores (targetTailChanges result) (rightStoreⁱ ρ)
      ⊢ applyCoercions (targetTailChanges result) (s ︔ t)
        ∶ applyTys (targetTailChanges result) C
          ⊒ applyTys (targetTailChanges result) D →
    μ ∣ resultRightCtx result ∣ rightStoreⁱ (resultStore result)
      ⊢ applyCoercions (targetTailChanges result) s ︔
          applyCoercions (targetTailChanges result) t
        ∶ applyTys (targetTailChanges result) C
          ⊒ applyTys (targetTailChanges result) D
  final-narrow-sequence result {s = s} {t = t} seq⊒ =
    subst
      (λ c → _ ∣ resultRightCtx result
        ∣ rightStoreⁱ (resultStore result)
        ⊢ c ∶ applyTys (targetTailChanges result) _
          ⊒ applyTys (targetTailChanges result) _)
      (apply-coercions-sequence (targetTailChanges result) s t)
      (subst
        (λ Δ → _ ∣ Δ ∣ rightStoreⁱ (resultStore result)
          ⊢ applyCoercions (targetTailChanges result) (s ︔ t)
            ∶ applyTys (targetTailChanges result) _
              ⊒ applyTys (targetTailChanges result) _)
        (sym (targetCtxResult result))
        (subst
          (λ Σ → _
            ∣ applyTyCtxs (targetTailChanges result) _ ∣ Σ
            ⊢ applyCoercions (targetTailChanges result) (s ︔ t)
              ∶ applyTys (targetTailChanges result) _
                ⊒ applyTys (targetTailChanges result) _)
          (sym (targetStoreResult result)) seq⊒))

  final-widen-sequence :
    ∀ {Φ Δᴸ Δᴿ V M′ A B}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      (result : WeakOneStepResult ρ V M′ A B keep)
      {μ C D s t} →
    μ ∣ applyTyCtxs (targetTailChanges result) Δᴿ
      ∣ applyStores (targetTailChanges result) (rightStoreⁱ ρ)
      ⊢ applyCoercions (targetTailChanges result) (s ︔ t)
        ∶ applyTys (targetTailChanges result) C
          ⊑ applyTys (targetTailChanges result) D →
    μ ∣ resultRightCtx result ∣ rightStoreⁱ (resultStore result)
      ⊢ applyCoercions (targetTailChanges result) s ︔
          applyCoercions (targetTailChanges result) t
        ∶ applyTys (targetTailChanges result) C
          ⊑ applyTys (targetTailChanges result) D
  final-widen-sequence result {s = s} {t = t} seq⊑ =
    subst
      (λ c → _ ∣ resultRightCtx result
        ∣ rightStoreⁱ (resultStore result)
        ⊢ c ∶ applyTys (targetTailChanges result) _
          ⊑ applyTys (targetTailChanges result) _)
      (apply-coercions-sequence (targetTailChanges result) s t)
      (subst
        (λ Δ → _ ∣ Δ ∣ rightStoreⁱ (resultStore result)
          ⊢ applyCoercions (targetTailChanges result) (s ︔ t)
            ∶ applyTys (targetTailChanges result) _
              ⊑ applyTys (targetTailChanges result) _)
        (sym (targetCtxResult result))
        (subst
          (λ Σ → _
            ∣ applyTyCtxs (targetTailChanges result) _ ∣ Σ
            ⊢ applyCoercions (targetTailChanges result) (s ︔ t)
              ∶ applyTys (targetTailChanges result) _
                ⊑ applyTys (targetTailChanges result) _)
          (sym (targetStoreResult result)) seq⊑))

  final-seal-mode :
    ∀ {Φ Δᴸ Δᴿ V M′ A B}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      (result : WeakOneStepResult ρ V M′ A B keep)
      {μ} →
    SealModeStore★ μ
      (applyStores (targetTailChanges result) (rightStoreⁱ ρ)) →
    SealModeStore★ μ (rightStoreⁱ (resultStore result))
  final-seal-mode result seal★ =
    subst (SealModeStore★ _)
      (sym (targetStoreResult result)) seal★

  narrow-sequence-resume :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
      {V M′ : Term} {A B D : Ty} {s t : Coercion} {μ : ModeEnv}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ A ⊑ D ⊣ Δᴿ} →
    WorldCoherentRightTargetPendingSequenceContinuation →
    StoreImpPrefix ρ₀ ρ⁺ →
    CastMode μ →
    SealModeStore★ μ (rightStoreⁱ ρ₀) →
    μ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ s ︔ t ∶ B ⊒ D →
    WorldCoherentRightValueCatchupIndexedResult
      {V = V} {M′ = M′} {ρ = ρ⁺} p →
    WorldCoherentRightValueCatchupIndexedResult
      {V = V} {M′ = M′ ⟨ s ︔ t ⟩} {ρ = ρ⁺} q
  narrow-sequence-resume {A = A} {p = p} {q = q}
      pending prefix mode seal★ seq⊒
      caught@(world-coherent-right-value-indexed-catchup
        (right-value-indexed-catchup indexed refl refl
          vV noV vW noW transport coherence)
        lineage bullet final-world final-exclusive final-wfR)
      with apply-narrows-typing
        { χs = keep ∷ targetTailChanges (weakIndexedResult indexed) }
        mode
        (seal★-weaken (rightStoreⁱ-prefix-inclusion prefix) seal★)
        (narrow-weaken ≤-refl
          (rightStoreⁱ-prefix-inclusion prefix) seq⊒)
  narrow-sequence-resume {A = A} {p = p} {q = q}
      pending prefix mode seal★ seq⊒
      caught@(world-coherent-right-value-indexed-catchup
        (right-value-indexed-catchup indexed refl refl
          vV noV vW noW transport coherence)
        lineage bullet final-world final-exclusive final-wfR)
      | μ′ , mode′ , seal★′ , seq⊒′
      with final-narrow-sequence (weakIndexedResult indexed) seq⊒′
  narrow-sequence-resume {A = A} {p = p} {q = q}
      pending prefix mode seal★ seq⊒
      caught@(world-coherent-right-value-indexed-catchup
        (right-value-indexed-catchup indexed refl refl
          vV noV vW noW transport coherence)
        lineage bullet final-world final-exclusive final-wfR)
      | μ′ , mode′ , seal★′ , seq⊒′
      | final-sequence@(C.cast-seq s⊢ t⊢ , sequence-narrowing)
      with split-narrowing-sequence sequence-narrowing
  narrow-sequence-resume {A = A} {p = p} {q = q}
      pending prefix mode seal★ seq⊒
      caught@(world-coherent-right-value-indexed-catchup
        (right-value-indexed-catchup indexed refl refl
          vV noV vW noW transport coherence)
        lineage bullet final-world final-exclusive final-wfR)
      | μ′ , mode′ , seal★′ , seq⊒′
      | final-sequence@(C.cast-seq s⊢ t⊢ , sequence-narrowing)
      | sⁿ , tⁿ
      with targetNarrowingAdministrationPlan
        target-administration-plan-synthesisᵀ
        { ρ₀ = resultStore (weakIndexedResult indexed) }
        { ρ⁺ = resultStore (weakIndexedResult indexed) }
        { A = A }
        { p = transportType (weakIndexedResult indexed) p }
        { q = transportType (weakIndexedResult indexed) q }
        prefix-reflⁱ final-wfR
        (final-seal-mode (weakIndexedResult indexed) seal★′)
        final-sequence
  narrow-sequence-resume {A = A} {p = p} {q = q}
      pending prefix mode seal★ seq⊒
      caught@(world-coherent-right-value-indexed-catchup
        (right-value-indexed-catchup indexed refl refl
          vV noV vW noW transport coherence)
        lineage bullet final-world final-exclusive final-wfR)
      | μ′ , mode′ , seal★′ , seq⊒′
      | final-sequence@(C.cast-seq s⊢ t⊢ , sequence-narrowing)
      | sⁿ , tⁿ | plan-seq s-plan t-plan =
    world-coherent-right-target-sequence-resume-proofᵀ
      caught continuation
    where
    result = weakIndexedResult indexed

    continuation =
      rightTargetPendingNarrowSequence pending
        (rightCatchupTargetValue
          (worldRightCatchupResult caught))
        mode′ (final-seal-mode result seal★′)
        (s⊢ , sⁿ) (t⊢ , tⁿ)
        s-plan t-plan
        (target-sequence-rank-decreases
          (rightCatchupTargetValue
            (worldRightCatchupResult caught))
          (applyCoercions (targetTailChanges result) _)
          (applyCoercions (targetTailChanges result) _) [])
        (canonicalIndexedResults indexed)
        final-world final-exclusive final-wfR
        (ok-no (no•-⟨⟩ (no•-⟨⟩ noW)))
        vV noV noW

  widen-sequence-resume :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
      {V M′ : Term} {A B D : Ty} {s t : Coercion} {μ : ModeEnv}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ A ⊑ D ⊣ Δᴿ} →
    WorldCoherentRightTargetPendingSequenceContinuation →
    StoreImpPrefix ρ₀ ρ⁺ →
    CastMode μ →
    SealModeStore★ μ (rightStoreⁱ ρ₀) →
    μ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ s ︔ t ∶ B ⊑ D →
    WorldCoherentRightValueCatchupIndexedResult
      {V = V} {M′ = M′} {ρ = ρ⁺} p →
    WorldCoherentRightValueCatchupIndexedResult
      {V = V} {M′ = M′ ⟨ s ︔ t ⟩} {ρ = ρ⁺} q
  widen-sequence-resume {A = A} {p = p} {q = q}
      pending prefix mode seal★ seq⊑
      caught@(world-coherent-right-value-indexed-catchup
        (right-value-indexed-catchup indexed refl refl
          vV noV vW noW transport coherence)
        lineage bullet final-world final-exclusive final-wfR)
      with apply-widens-typing
        { χs = keep ∷ targetTailChanges (weakIndexedResult indexed) }
        mode
        (seal★-weaken (rightStoreⁱ-prefix-inclusion prefix) seal★)
        (widen-weaken ≤-refl
          (rightStoreⁱ-prefix-inclusion prefix) seq⊑)
  widen-sequence-resume {A = A} {p = p} {q = q}
      pending prefix mode seal★ seq⊑
      caught@(world-coherent-right-value-indexed-catchup
        (right-value-indexed-catchup indexed refl refl
          vV noV vW noW transport coherence)
        lineage bullet final-world final-exclusive final-wfR)
      | μ′ , mode′ , seal★′ , seq⊑′
      with final-widen-sequence (weakIndexedResult indexed) seq⊑′
  widen-sequence-resume {A = A} {p = p} {q = q}
      pending prefix mode seal★ seq⊑
      caught@(world-coherent-right-value-indexed-catchup
        (right-value-indexed-catchup indexed refl refl
          vV noV vW noW transport coherence)
        lineage bullet final-world final-exclusive final-wfR)
      | μ′ , mode′ , seal★′ , seq⊑′
      | final-sequence@(C.cast-seq s⊢ t⊢ , sequence-widening)
      with split-widening-sequence sequence-widening
  widen-sequence-resume {A = A} {p = p} {q = q}
      pending prefix mode seal★ seq⊑
      caught@(world-coherent-right-value-indexed-catchup
        (right-value-indexed-catchup indexed refl refl
          vV noV vW noW transport coherence)
        lineage bullet final-world final-exclusive final-wfR)
      | μ′ , mode′ , seal★′ , seq⊑′
      | final-sequence@(C.cast-seq s⊢ t⊢ , sequence-widening)
      | sʷ , tʷ
      with targetWideningAdministrationPlan
        target-administration-plan-synthesisᵀ
        { ρ₀ = resultStore (weakIndexedResult indexed) }
        { ρ⁺ = resultStore (weakIndexedResult indexed) }
        { A = A }
        { p = transportType (weakIndexedResult indexed) p }
        { q = transportType (weakIndexedResult indexed) q }
        prefix-reflⁱ final-wfR
        (final-seal-mode (weakIndexedResult indexed) seal★′)
        final-sequence
  widen-sequence-resume {A = A} {p = p} {q = q}
      pending prefix mode seal★ seq⊑
      caught@(world-coherent-right-value-indexed-catchup
        (right-value-indexed-catchup indexed refl refl
          vV noV vW noW transport coherence)
        lineage bullet final-world final-exclusive final-wfR)
      | μ′ , mode′ , seal★′ , seq⊑′
      | final-sequence@(C.cast-seq s⊢ t⊢ , sequence-widening)
      | sʷ , tʷ | plan-seq s-plan t-plan =
    world-coherent-right-target-sequence-resume-proofᵀ
      caught continuation
    where
    result = weakIndexedResult indexed

    continuation =
      rightTargetPendingWidenSequence pending
        (rightCatchupTargetValue
          (worldRightCatchupResult caught))
        mode′ (final-seal-mode result seal★′)
        (s⊢ , sʷ) (t⊢ , tʷ)
        s-plan t-plan
        (target-sequence-rank-decreases
          (rightCatchupTargetValue
            (worldRightCatchupResult caught))
          (applyCoercions (targetTailChanges result) _)
          (applyCoercions (targetTailChanges result) _) [])
        (canonicalIndexedResults indexed)
        final-world final-exclusive final-wfR
        (ok-no (no•-⟨⟩ (no•-⟨⟩ noW)))
        vV noV noW

  id-widen-sequence-resume :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
      {V M′ : Term} {A B D : Ty} {s t : Coercion}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ A ⊑ D ⊣ Δᴿ} →
    WorldCoherentRightTargetPendingSequenceContinuation →
    StoreImpPrefix ρ₀ ρ⁺ →
    SealModeStore★ id-onlyᵈ (rightStoreⁱ ρ₀) →
    id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ s ︔ t ∶ B ⊑ D →
    WorldCoherentRightValueCatchupIndexedResult
      {V = V} {M′ = M′} {ρ = ρ⁺} p →
    WorldCoherentRightValueCatchupIndexedResult
      {V = V} {M′ = M′ ⟨ s ︔ t ⟩} {ρ = ρ⁺} q
  id-widen-sequence-resume {A = A} {p = p} {q = q}
      pending prefix seal★ seq⊑
      caught@(world-coherent-right-value-indexed-catchup
        (right-value-indexed-catchup indexed refl refl
          vV noV vW noW transport coherence)
        lineage bullet final-world final-exclusive final-wfR)
      with final-widen-sequence (weakIndexedResult indexed)
        (apply-fixed-widens-typing
          { χs = keep ∷
            targetTailChanges (weakIndexedResult indexed) }
          (modeRename-id-only suc)
          (widen-weaken ≤-refl
            (rightStoreⁱ-prefix-inclusion prefix) seq⊑))
  id-widen-sequence-resume {A = A} {p = p} {q = q}
      pending prefix seal★ seq⊑
      caught@(world-coherent-right-value-indexed-catchup
        (right-value-indexed-catchup indexed refl refl
          vV noV vW noW transport coherence)
        lineage bullet final-world final-exclusive final-wfR)
      | final-sequence@(C.cast-seq s⊢ t⊢ , sequence-widening)
      with split-widening-sequence sequence-widening
  id-widen-sequence-resume {A = A} {p = p} {q = q}
      pending prefix seal★ seq⊑
      caught@(world-coherent-right-value-indexed-catchup
        (right-value-indexed-catchup indexed refl refl
          vV noV vW noW transport coherence)
        lineage bullet final-world final-exclusive final-wfR)
      | final-sequence@(C.cast-seq s⊢ t⊢ , sequence-widening)
      | sʷ , tʷ
      with targetWideningAdministrationPlan
        target-administration-plan-synthesisᵀ
        { ρ₀ = resultStore (weakIndexedResult indexed) }
        { ρ⁺ = resultStore (weakIndexedResult indexed) }
        { A = A }
        { p = transportType (weakIndexedResult indexed) p }
        { q = transportType (weakIndexedResult indexed) q }
        prefix-reflⁱ final-wfR seal★-id-only final-sequence
  id-widen-sequence-resume {A = A} {p = p} {q = q}
      pending prefix seal★ seq⊑
      caught@(world-coherent-right-value-indexed-catchup
        (right-value-indexed-catchup indexed refl refl
          vV noV vW noW transport coherence)
        lineage bullet final-world final-exclusive final-wfR)
      | final-sequence@(C.cast-seq s⊢ t⊢ , sequence-widening)
      | sʷ , tʷ | plan-seq s-plan t-plan =
    world-coherent-right-target-sequence-resume-proofᵀ
      caught continuation
    where
    result = weakIndexedResult indexed

    continuation =
      rightTargetPendingIdWidenSequence pending
        (rightCatchupTargetValue
          (worldRightCatchupResult caught))
        seal★-id-only (s⊢ , sʷ) (t⊢ , tʷ)
        s-plan t-plan
        (target-sequence-rank-decreases
          (rightCatchupTargetValue
            (worldRightCatchupResult caught))
          (applyCoercions (targetTailChanges result) _)
          (applyCoercions (targetTailChanges result) _) [])
        (canonicalIndexedResults indexed)
        final-world final-exclusive final-wfR
        (ok-no (no•-⟨⟩ (no•-⟨⟩ noW)))
        vV noV noW

  narrow-administration :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
      {V M′ : Term} {A B C : Ty} {c : Coercion} {μ : ModeEnv}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ A ⊑ C ⊣ Δᴿ} →
    WorldCoherentRightTargetInertFramingᵀ →
    WorldCoherentRightTargetPendingSequenceContinuation →
    WorldCoherentRightTargetActiveRootResume →
    StoreImpPrefix ρ₀ ρ⁺ →
    WorldCoherent ρ⁺ →
    SourceNameExclusive Φ →
    StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
    RuntimeOK (M′ ⟨ c ⟩) →
    Value V →
    No• V →
    CastMode μ →
    SealModeStore★ μ (rightStoreⁱ ρ₀) →
    (c⊒ : μ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ c ∶ B ⊒ C) →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
      ⊢ᴺ V ⊑ M′ ⦂ A ⊑ B ∶ p →
    WorldCoherentRightValueCatchupIndexedResult
      {V = V} {M′ = M′} {ρ = ρ⁺} p →
    TargetAdministrationPlan ρ₀ A (proj₁ c⊒) p q →
    WorldCoherentRightValueCatchupIndexedResult
      {V = V} {M′ = M′ ⟨ c ⟩} {ρ = ρ⁺} q
  narrow-administration inert pending roots prefix coherent exclusive wfR
      runtime vV noV mode seal★ c⊒ relation caught (plan-inert c-inert) =
    inert prefix c-inert
      (inj₂ (inj₂ (inj₁ (_ , mode , seal★ , c⊒)))) caught
  narrow-administration inert pending roots prefix coherent exclusive wfR
      runtime vV noV mode seal★ c⊒ relation caught plan-id =
    rightTargetNarrowIdentityRoot roots prefix coherent exclusive wfR
      runtime vV noV mode seal★ c⊒ relation caught
  narrow-administration inert pending roots prefix coherent exclusive wfR
      runtime vV noV mode seal★ c⊒ relation caught plan-untag =
    rightTargetNarrowUntagRoot roots prefix coherent exclusive wfR
      runtime vV noV mode seal★ c⊒ relation caught
  narrow-administration inert pending roots prefix coherent exclusive wfR
      runtime vV noV mode seal★
      (C.cast-unseal hB αB∈Σ ok , NW.cross ())
      relation caught plan-unseal
  narrow-administration inert pending roots prefix coherent exclusive wfR
      runtime vV noV mode seal★
      (C.cast-inst hB occ s⊢ , NW.cross ()) relation caught plan-inst
  narrow-administration inert pending roots prefix coherent exclusive wfR
      runtime vV noV mode seal★ c⊒ relation caught
      (plan-seq s-plan t-plan) =
    narrow-sequence-resume pending prefix mode seal★ c⊒ caught

  widen-administration :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
      {V M′ : Term} {A B C : Ty} {c : Coercion} {μ : ModeEnv}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ A ⊑ C ⊣ Δᴿ} →
    WorldCoherentRightTargetInertFramingᵀ →
    WorldCoherentRightTargetPendingSequenceContinuation →
    WorldCoherentRightTargetActiveRootResume →
    WorldCoherentRightTargetAllocationFrames →
    StoreImpPrefix ρ₀ ρ⁺ →
    WorldCoherent ρ⁺ →
    SourceNameExclusive Φ →
    StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
    RuntimeOK (M′ ⟨ c ⟩) →
    Value V →
    No• V →
    CastMode μ →
    SealModeStore★ μ (rightStoreⁱ ρ₀) →
    (c⊑ : μ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ c ∶ B ⊑ C) →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
      ⊢ᴺ V ⊑ M′ ⦂ A ⊑ B ∶ p →
    WorldCoherentRightValueCatchupIndexedResult
      {V = V} {M′ = M′} {ρ = ρ⁺} p →
    TargetAdministrationPlan ρ₀ A (proj₁ c⊑) p q →
    WorldCoherentRightValueCatchupIndexedResult
      {V = V} {M′ = M′ ⟨ c ⟩} {ρ = ρ⁺} q
  widen-administration inert pending roots allocation prefix coherent
      exclusive wfR runtime vV noV mode seal★ c⊑ relation caught
      (plan-inert c-inert) =
    inert prefix c-inert
      (inj₂ (inj₂ (inj₂
        (inj₁ (_ , mode , seal★ , c⊑))))) caught
  widen-administration inert pending roots allocation prefix coherent
      exclusive wfR runtime vV noV mode seal★ c⊑ relation caught
      plan-id =
    rightTargetWidenIdentityRoot roots prefix coherent exclusive wfR
      runtime vV noV mode seal★ c⊑ relation caught
  widen-administration inert pending roots allocation prefix coherent
      exclusive wfR runtime vV noV mode seal★
      (C.cast-untag hH gH ok , NW.cross ()) relation caught plan-untag
  widen-administration inert pending roots allocation prefix coherent
      exclusive wfR runtime vV noV mode seal★ c⊑ relation caught
      plan-unseal =
    rightTargetWidenUnsealRoot roots prefix coherent exclusive wfR
      runtime vV noV mode seal★ c⊑ relation caught
  widen-administration inert pending roots allocation prefix coherent
      exclusive wfR runtime vV noV mode seal★ c⊑ relation caught
      plan-inst =
    rightTargetWidenInstantiationRoot roots allocation prefix coherent
      exclusive wfR runtime vV noV mode seal★ c⊑ relation caught
  widen-administration inert pending roots allocation prefix coherent
      exclusive wfR runtime vV noV mode seal★ c⊑ relation caught
      (plan-seq s-plan t-plan) =
    widen-sequence-resume pending prefix mode seal★ c⊑ caught

  id-widen-administration :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
      {V M′ : Term} {A B C : Ty} {c : Coercion}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ A ⊑ C ⊣ Δᴿ} →
    WorldCoherentRightTargetInertFramingᵀ →
    WorldCoherentRightTargetPendingSequenceContinuation →
    WorldCoherentRightTargetActiveRootResume →
    WorldCoherentRightTargetAllocationFrames →
    StoreImpPrefix ρ₀ ρ⁺ →
    WorldCoherent ρ⁺ →
    SourceNameExclusive Φ →
    StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
    RuntimeOK (M′ ⟨ c ⟩) →
    Value V →
    No• V →
    SealModeStore★ id-onlyᵈ (rightStoreⁱ ρ₀) →
    (c⊑ : id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
      ⊢ c ∶ B ⊑ C) →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
      ⊢ᴺ V ⊑ M′ ⦂ A ⊑ B ∶ p →
    WorldCoherentRightValueCatchupIndexedResult
      {V = V} {M′ = M′} {ρ = ρ⁺} p →
    TargetAdministrationPlan ρ₀ A (proj₁ c⊑) p q →
    WorldCoherentRightValueCatchupIndexedResult
      {V = V} {M′ = M′ ⟨ c ⟩} {ρ = ρ⁺} q
  id-widen-administration inert pending roots allocation prefix coherent
      exclusive wfR runtime vV noV seal★ c⊑ relation caught
      (plan-inert c-inert) =
    inert prefix c-inert
      (inj₂ (inj₂ (inj₂ (inj₂ (seal★ , c⊑))))) caught
  id-widen-administration inert pending roots allocation prefix coherent
      exclusive wfR runtime vV noV seal★ c⊑ relation caught plan-id =
    rightTargetIdWidenIdentityRoot roots prefix coherent exclusive wfR
      runtime vV noV seal★ c⊑ relation caught
  id-widen-administration inert pending roots allocation prefix coherent
      exclusive wfR runtime vV noV seal★
      (C.cast-untag hH gH ok , NW.cross ()) relation caught plan-untag
  id-widen-administration inert pending roots allocation prefix coherent
      exclusive wfR runtime vV noV seal★
      (C.cast-unseal hB αB∈Σ () , cʷ) relation caught plan-unseal
  id-widen-administration inert pending roots allocation prefix coherent
      exclusive wfR runtime vV noV seal★ c⊑ relation caught plan-inst =
    rightTargetIdWidenInstantiationRoot roots allocation prefix coherent
      exclusive wfR runtime vV noV seal★ c⊑ relation caught
  id-widen-administration inert pending roots allocation prefix coherent
      exclusive wfR runtime vV noV seal★ c⊑ relation caught
      (plan-seq s-plan t-plan) =
    id-widen-sequence-resume pending prefix seal★ c⊑ caught

  reveal-administration :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
      {V M′ : Term} {A B C : Ty} {c : Coercion} {μ β X}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ A ⊑ C ⊣ Δᴿ} →
    WorldCoherentRightTargetInertFramingᵀ →
    WorldCoherentRightTargetActiveRootResume →
    StoreImpPrefix ρ₀ ρ⁺ →
    WorldCoherent ρ⁺ →
    SourceNameExclusive Φ →
    StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
    RuntimeOK (M′ ⟨ c ⟩) →
    Value V →
    No• V →
    RevealConversion μ Δᴿ (rightStoreⁱ ρ₀) β X c B C →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
      ⊢ᴺ V ⊑ M′ ⦂ A ⊑ B ∶ p →
    WorldCoherentRightValueCatchupIndexedResult
      {V = V} {M′ = M′} {ρ = ρ⁺} p →
    WorldCoherentRightValueCatchupIndexedResult
      {V = V} {M′ = M′ ⟨ c ⟩} {ρ = ρ⁺} q
  reveal-administration inert roots prefix coherent exclusive wfR runtime
      vV noV c↑@(reveal-id-var hY ok) relation caught =
    rightTargetRevealIdentityRoot roots prefix coherent exclusive wfR
      runtime vV noV c↑ relation caught
  reveal-administration inert roots prefix coherent exclusive wfR runtime
      vV noV c↑@reveal-id-base relation caught =
    rightTargetRevealIdentityRoot roots prefix coherent exclusive wfR
      runtime vV noV c↑ relation caught
  reveal-administration inert roots prefix coherent exclusive wfR runtime
      vV noV c↑@reveal-id-★ relation caught =
    rightTargetRevealIdentityRoot roots prefix coherent exclusive wfR
      runtime vV noV c↑ relation caught
  reveal-administration inert roots prefix coherent exclusive wfR runtime
      vV noV c↑@(reveal-unseal hC α∈Σ ok) relation caught =
    rightTargetRevealUnsealRoot roots prefix coherent exclusive wfR
      runtime vV noV c↑ relation caught
  reveal-administration inert roots prefix coherent exclusive wfR runtime
      vV noV c↑@(reveal-fun {s = s} {t = t} s↓ t↑)
      relation caught =
    inert prefix (s C.↦ t) (inj₁ (_ , _ , _ , c↑)) caught
  reveal-administration inert roots prefix coherent exclusive wfR runtime
      vV noV c↑@(reveal-all {s = s} s↑) relation caught =
    inert prefix (C.`∀ s) (inj₁ (_ , _ , _ , c↑)) caught

  conceal-administration :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
      {V M′ : Term} {A B C : Ty} {c : Coercion} {μ β X}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ A ⊑ C ⊣ Δᴿ} →
    WorldCoherentRightTargetInertFramingᵀ →
    WorldCoherentRightTargetActiveRootResume →
    StoreImpPrefix ρ₀ ρ⁺ →
    WorldCoherent ρ⁺ →
    SourceNameExclusive Φ →
    StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
    RuntimeOK (M′ ⟨ c ⟩) →
    Value V →
    No• V →
    ConcealConversion μ Δᴿ (rightStoreⁱ ρ₀) β X c B C →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
      ⊢ᴺ V ⊑ M′ ⦂ A ⊑ B ∶ p →
    WorldCoherentRightValueCatchupIndexedResult
      {V = V} {M′ = M′} {ρ = ρ⁺} p →
    WorldCoherentRightValueCatchupIndexedResult
      {V = V} {M′ = M′ ⟨ c ⟩} {ρ = ρ⁺} q
  conceal-administration inert roots prefix coherent exclusive wfR runtime
      vV noV c↓@(conceal-id-var hY ok) relation caught =
    rightTargetConcealIdentityRoot roots prefix coherent exclusive wfR
      runtime vV noV c↓ relation caught
  conceal-administration inert roots prefix coherent exclusive wfR runtime
      vV noV c↓@conceal-id-base relation caught =
    rightTargetConcealIdentityRoot roots prefix coherent exclusive wfR
      runtime vV noV c↓ relation caught
  conceal-administration inert roots prefix coherent exclusive wfR runtime
      vV noV c↓@conceal-id-★ relation caught =
    rightTargetConcealIdentityRoot roots prefix coherent exclusive wfR
      runtime vV noV c↓ relation caught
  conceal-administration { β = β } {X = X}
      inert roots prefix coherent exclusive wfR runtime vV noV
      c↓@(conceal-seal hX β∈Σ ok) relation caught =
    inert prefix (C.seal X β)
      (inj₂ (inj₁ (_ , _ , _ , c↓))) caught
  conceal-administration inert roots prefix coherent exclusive wfR runtime
      vV noV c↓@(conceal-fun {s = s} {t = t} s↑ t↓)
      relation caught =
    inert prefix (s C.↦ t)
      (inj₂ (inj₁ (_ , _ , _ , c↓))) caught
  conceal-administration inert roots prefix coherent exclusive wfR runtime
      vV noV c↓@(conceal-all {s = s} s↓) relation caught =
    inert prefix (C.`∀ s)
      (inj₂ (inj₁ (_ , _ , _ , c↓))) caught


world-coherent-right-target-cast-terminalization-proofᵀ :
  WorldCoherentRightTargetInertFramingᵀ →
  WorldCoherentRightTargetPendingSequenceContinuation →
  WorldCoherentRightTargetActiveRootResume →
  WorldCoherentRightTargetAllocationFrames →
  WorldCoherentRightTargetCastTerminalization
world-coherent-right-target-cast-terminalization-proofᵀ
    inert pending roots allocation =
  record
    { rightTargetNarrowFrame =
        λ prefix coherent exclusive wfR runtime vV noV mode seal★ c⊒
          relation caught →
        narrow-administration inert pending roots prefix coherent exclusive
          wfR runtime vV noV mode seal★ c⊒ relation caught
          (targetNarrowingAdministrationPlan
            target-administration-plan-synthesisᵀ
            prefix wfR seal★ c⊒)
    ; rightTargetWidenFrame =
        λ prefix coherent exclusive wfR runtime vV noV mode seal★ c⊑
          relation caught →
        widen-administration inert pending roots allocation prefix coherent
          exclusive wfR runtime vV noV mode seal★ c⊑ relation caught
          (targetWideningAdministrationPlan
            target-administration-plan-synthesisᵀ
            prefix wfR seal★ c⊑)
    ; rightTargetIdWidenFrame =
        λ prefix coherent exclusive wfR runtime vV noV seal★ c⊑
          relation caught →
        id-widen-administration inert pending roots allocation prefix
          coherent exclusive wfR runtime vV noV seal★ c⊑ relation caught
          (targetWideningAdministrationPlan
            target-administration-plan-synthesisᵀ
            prefix wfR seal★ c⊑)
    ; rightTargetRevealFrame =
        λ prefix coherent exclusive wfR runtime vV noV c↑ relation caught →
        reveal-administration inert roots prefix coherent exclusive wfR
          runtime vV noV c↑ relation caught
    ; rightTargetConcealFrame =
        λ prefix coherent exclusive wfR runtime vV noV c↓ relation caught →
        conceal-administration inert roots prefix coherent exclusive wfR
          runtime vV noV c↓ relation caught
    }

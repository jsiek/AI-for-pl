module
  proof.WorldCoherent.Right.Target.Terminalization.NuImprecisionWorldCoherentRightTargetCastTerminalizationProof
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
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import Coercions as C
open import Coercions using
  (Coercion; ModeEnv; id-onlyᵈ; _︔_; _∣_∣_⊢_∶_=⇒_)
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
  (StoreImp; rightStoreⁱ; seal★-tag-or-id)
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
  (CastMode; SealModeStore★; cast-tag-or-id)
open import Types using (Ty; TyCtx)
import Types as T
open import proof.Core.Properties.CoercionProperties using
  (ModeRename; coercion-endpoints-unique; modeRename-id-only)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import proof.Catchup.Simulation.NuImprecisionSimulationCore using
  (apply-narrows-typing; seal★-id-only)
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  (rightStoreⁱ-prefix-inclusion)
open import proof.Target.Administration.NuImprecisionTargetAdministrationMeasureProof using
  (target-sequence-rank-decreases)
open import proof.Target.Administration.NuImprecisionTargetAdministrationPlanDef using
  ( TargetAdministrationPlan
  ; plan-fun-untag-gen
  ; plan-id
  ; plan-inert
  ; plan-inst
  ; plan-inst-fun-tag
  ; plan-seq
  ; plan-unseal
  ; plan-untag
  )
open import proof.Target.Administration.NuImprecisionTargetAdministrationPlanSynthesisDef using
  ( targetNarrowingAdministrationPlan
  ; targetWideningAdministrationPlan
  )
open import proof.Target.Administration.NuImprecisionTargetAdministrationPlanSynthesisLemma using
  (target-administration-plan-synthesisᵀ)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.Right.ValueCatchup.NuImprecisionRightValueCatchupResultDef using
  ( right-value-indexed-catchup
  ; rightCatchupIndexedResult
  ; rightCatchupSourceNoBullet
  ; rightCatchupSourceValue
  ; rightCatchupTargetNoBullet
  ; rightCatchupTargetValue
  )
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
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
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightCatchupResultDef
  using
  ( WorldCoherentRightValueCatchupIndexedResult
  ; world-coherent-right-value-indexed-catchup
  ; worldRightCatchupCoherence
  ; worldRightCatchupResult
  ; worldRightCatchupSourceNameExclusive
  ; worldRightCatchupTargetStoreWf
  )
open import
  proof.WorldCoherent.Right.Target.ActiveRoots.NuImprecisionWorldCoherentRightTargetActiveRootResumeDef
open import
  proof.WorldCoherent.Right.Target.ActiveRoots.NuImprecisionWorldCoherentRightTargetAllocationFramesDef
  using (WorldCoherentRightTargetAllocationFrames)
open import
  proof.WorldCoherent.Right.Target.Terminalization.NuImprecisionWorldCoherentRightTargetCastTerminalizationDef
  using (WorldCoherentRightTargetCastTerminalization)
open import
  proof.WorldCoherent.Right.Target.Framing.NuImprecisionWorldCoherentRightTargetInertFramingDef
  using (WorldCoherentRightTargetInertFramingᵀ)
open import
  proof.WorldCoherent.Right.Target.Resume.NuImprecisionWorldCoherentRightTargetPendingSequenceContinuationDef
open import
  proof.WorldCoherent.Right.Target.Resume.NuImprecisionWorldCoherentRightTargetSequenceResumeProof
  using (world-coherent-right-target-sequence-resume-proofᵀ)
open import proof.Core.Properties.NuWideningTransport using
  (apply-fixed-widens-typing; apply-widens-typing)
open import proof.Core.Properties.ReductionProperties using
  ( applyCoercions
  ; applyCoercions-preserves-Inert
  )
open import proof.Core.Properties.TypePreservation using (seal★-weaken)


private
  split-narrowing-sequence :
    ∀ {s t} → Narrowing (s ︔ t) → Narrowing s × Narrowing t
  split-narrowing-sequence (gG NW.？︔ gⁿ) =
    NW.untag gG , strictⁿ→narrow (NW.strict-crossⁿ gⁿ)
  split-narrowing-sequence (NW.fun-untag-gen safe) =
    NW.untag T.★⇒★ , NW.gen safe
  split-narrowing-sequence (sⁿ NW.︔seal α) =
    strictⁿ→narrow sⁿ , NW.sealⁿ _ α

  split-widening-sequence :
    ∀ {s t} → Widening (s ︔ t) → Widening s × Widening t
  split-widening-sequence (sʷ NW.︔ gG !) =
    strictʷ→widen (NW.strict-crossʷ sʷ) , NW.tag gG
  split-widening-sequence (NW.inst-fun-tag safe) =
    NW.inst safe , NW.tag T.★⇒★
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

  apply-narrow-sequence-components :
    ∀ {χs μ Δ Σ Σ′ s t A B C} →
    StoreIncl Σ Σ′ →
    CastMode μ →
    SealModeStore★ μ Σ′ →
    μ ∣ Δ ∣ Σ ⊢ s ∶ A =⇒ B →
    μ ∣ Δ ∣ Σ ⊢ t ∶ B =⇒ C →
    Narrowing (s ︔ t) →
    ∃[ μ′ ]
      CastMode μ′ ×
      SealModeStore★ μ′ (applyStores χs Σ′) ×
      (μ′ ∣ applyTyCtxs χs Δ ∣ applyStores χs Σ′
        ⊢ applyCoercions χs s ∶ applyTys χs A ⊒ applyTys χs B) ×
      (μ′ ∣ applyTyCtxs χs Δ ∣ applyStores χs Σ′
        ⊢ applyCoercions χs t ∶ applyTys χs B ⊒ applyTys χs C)
  apply-narrow-sequence-components
      {χs = χs} {Δ = Δ} {Σ′ = Σ′} {s = s} {t = t}
      {A = A} {B = B} {C = C}
      incl mode seal★ s⊢ t⊢ sequence-narrowing
      with split-narrowing-sequence sequence-narrowing
  apply-narrow-sequence-components
      {χs = χs} {Δ = Δ} {Σ′ = Σ′} {s = s} {t = t}
      {A = A} {B = B} {C = C}
      incl mode seal★ s⊢ t⊢ sequence-narrowing
      | sⁿ , tⁿ
      with apply-narrows-typing {χs = χs} mode seal★
        (narrow-weaken ≤-refl incl
          (C.cast-seq s⊢ t⊢ , sequence-narrowing))
  apply-narrow-sequence-components
      {χs = χs} {Δ = Δ} {Σ′ = Σ′} {s = s} {t = t}
      {A = A} {B = B} {C = C}
      incl mode seal★ s⊢ t⊢ sequence-narrowing
      | sⁿ , tⁿ
      | μ′ , mode′ , seal★′ , sequence′
      with subst
        (λ c → μ′ ∣ applyTyCtxs χs Δ ∣ applyStores χs Σ′
          ⊢ c ∶ applyTys χs A ⊒ applyTys χs C)
        (apply-coercions-sequence χs s t) sequence′
  apply-narrow-sequence-components
      {χs = χs} {Δ = Δ} {Σ′ = Σ′} {s = s} {t = t}
      {A = A} {B = B} {C = C}
      incl mode seal★ s⊢ t⊢ sequence-narrowing
      | sⁿ , tⁿ
      | μ′ , mode′ , seal★′ , sequence′
      | C.cast-seq s′⊢ t′⊢ , sequence-narrowing′
      with split-narrowing-sequence sequence-narrowing′
  apply-narrow-sequence-components
      {χs = χs} {Δ = Δ} {Σ′ = Σ′} {s = s} {t = t}
      {A = A} {B = B} {C = C}
      incl mode seal★ s⊢ t⊢ sequence-narrowing
      | sⁿ , tⁿ
      | μ′ , mode′ , seal★′ , sequence′
      | C.cast-seq s′⊢ t′⊢ , sequence-narrowing′
      | s′ⁿ , t′ⁿ
      with apply-narrows-typing {χs = χs} mode seal★
        (narrow-weaken ≤-refl incl (s⊢ , sⁿ))
         | apply-narrows-typing {χs = χs} mode seal★
        (narrow-weaken ≤-refl incl (t⊢ , tⁿ))
  apply-narrow-sequence-components
      {χs = χs} {Δ = Δ} {Σ′ = Σ′} {s = s} {t = t}
      {A = A} {B = B} {C = C}
      incl mode seal★ s⊢ t⊢ sequence-narrowing
      | sⁿ , tⁿ
      | μ′ , mode′ , seal★′ , sequence′
      | C.cast-seq s′⊢ t′⊢ , sequence-narrowing′
      | s′ⁿ , t′ⁿ
      | μˢ , modeˢ , seal★ˢ , s-expected
      | μᵗ , modeᵗ , seal★ᵗ , t-expected
      with coercion-endpoints-unique (μ′ , s′⊢)
        (μˢ , proj₁ s-expected)
         | coercion-endpoints-unique (μ′ , t′⊢)
        (μᵗ , proj₁ t-expected)
  apply-narrow-sequence-components
      {χs = χs} {Δ = Δ} {Σ′ = Σ′} {s = s} {t = t}
      {A = A} {B = B} {C = C}
      incl mode seal★ s⊢ t⊢ sequence-narrowing
      | sⁿ , tⁿ
      | μ′ , mode′ , seal★′ , sequence′
      | C.cast-seq s′⊢ t′⊢ , sequence-narrowing′
      | s′ⁿ , t′ⁿ
      | μˢ , modeˢ , seal★ˢ , s-expected
      | μᵗ , modeᵗ , seal★ᵗ , t-expected
      | s-src≡ , s-tgt≡ | t-src≡ , t-tgt≡ =
    μ′ , mode′ , seal★′ ,
    (subst
      (λ X → μ′ ∣ applyTyCtxs χs Δ ∣ applyStores χs Σ′
        ⊢ applyCoercions χs s ∶ applyTys χs A =⇒ X)
      s-tgt≡ s′⊢ , s′ⁿ) ,
    (subst
      (λ X → μ′ ∣ applyTyCtxs χs Δ ∣ applyStores χs Σ′
        ⊢ applyCoercions χs t ∶ X =⇒ applyTys χs C)
      t-src≡ t′⊢ , t′ⁿ)

  apply-widen-sequence-components :
    ∀ {χs μ Δ Σ Σ′ s t A B C} →
    StoreIncl Σ Σ′ →
    CastMode μ →
    SealModeStore★ μ Σ′ →
    μ ∣ Δ ∣ Σ ⊢ s ∶ A =⇒ B →
    μ ∣ Δ ∣ Σ ⊢ t ∶ B =⇒ C →
    Widening (s ︔ t) →
    ∃[ μ′ ]
      CastMode μ′ ×
      SealModeStore★ μ′ (applyStores χs Σ′) ×
      (μ′ ∣ applyTyCtxs χs Δ ∣ applyStores χs Σ′
        ⊢ applyCoercions χs s ∶ applyTys χs A ⊑ applyTys χs B) ×
      (μ′ ∣ applyTyCtxs χs Δ ∣ applyStores χs Σ′
        ⊢ applyCoercions χs t ∶ applyTys χs B ⊑ applyTys χs C)
  apply-widen-sequence-components
      {χs = χs} {Δ = Δ} {Σ′ = Σ′} {s = s} {t = t}
      {A = A} {B = B} {C = C}
      incl mode seal★ s⊢ t⊢ sequence-widening
      with split-widening-sequence sequence-widening
  apply-widen-sequence-components
      {χs = χs} {Δ = Δ} {Σ′ = Σ′} {s = s} {t = t}
      {A = A} {B = B} {C = C}
      incl mode seal★ s⊢ t⊢ sequence-widening
      | sʷ , tʷ
      with apply-widens-typing {χs = χs} mode seal★
        (widen-weaken ≤-refl incl
          (C.cast-seq s⊢ t⊢ , sequence-widening))
  apply-widen-sequence-components
      {χs = χs} {Δ = Δ} {Σ′ = Σ′} {s = s} {t = t}
      {A = A} {B = B} {C = C}
      incl mode seal★ s⊢ t⊢ sequence-widening
      | sʷ , tʷ
      | μ′ , mode′ , seal★′ , sequence′
      with subst
        (λ c → μ′ ∣ applyTyCtxs χs Δ ∣ applyStores χs Σ′
          ⊢ c ∶ applyTys χs A ⊑ applyTys χs C)
        (apply-coercions-sequence χs s t) sequence′
  apply-widen-sequence-components
      {χs = χs} {Δ = Δ} {Σ′ = Σ′} {s = s} {t = t}
      {A = A} {B = B} {C = C}
      incl mode seal★ s⊢ t⊢ sequence-widening
      | sʷ , tʷ
      | μ′ , mode′ , seal★′ , sequence′
      | C.cast-seq s′⊢ t′⊢ , sequence-widening′
      with split-widening-sequence sequence-widening′
  apply-widen-sequence-components
      {χs = χs} {Δ = Δ} {Σ′ = Σ′} {s = s} {t = t}
      {A = A} {B = B} {C = C}
      incl mode seal★ s⊢ t⊢ sequence-widening
      | sʷ , tʷ
      | μ′ , mode′ , seal★′ , sequence′
      | C.cast-seq s′⊢ t′⊢ , sequence-widening′
      | s′ʷ , t′ʷ
      with apply-widens-typing {χs = χs} mode seal★
        (widen-weaken ≤-refl incl (s⊢ , sʷ))
         | apply-widens-typing {χs = χs} mode seal★
        (widen-weaken ≤-refl incl (t⊢ , tʷ))
  apply-widen-sequence-components
      {χs = χs} {Δ = Δ} {Σ′ = Σ′} {s = s} {t = t}
      {A = A} {B = B} {C = C}
      incl mode seal★ s⊢ t⊢ sequence-widening
      | sʷ , tʷ
      | μ′ , mode′ , seal★′ , sequence′
      | C.cast-seq s′⊢ t′⊢ , sequence-widening′
      | s′ʷ , t′ʷ
      | μˢ , modeˢ , seal★ˢ , s-expected
      | μᵗ , modeᵗ , seal★ᵗ , t-expected
      with coercion-endpoints-unique (μ′ , s′⊢)
        (μˢ , proj₁ s-expected)
         | coercion-endpoints-unique (μ′ , t′⊢)
        (μᵗ , proj₁ t-expected)
  apply-widen-sequence-components
      {χs = χs} {Δ = Δ} {Σ′ = Σ′} {s = s} {t = t}
      {A = A} {B = B} {C = C}
      incl mode seal★ s⊢ t⊢ sequence-widening
      | sʷ , tʷ
      | μ′ , mode′ , seal★′ , sequence′
      | C.cast-seq s′⊢ t′⊢ , sequence-widening′
      | s′ʷ , t′ʷ
      | μˢ , modeˢ , seal★ˢ , s-expected
      | μᵗ , modeᵗ , seal★ᵗ , t-expected
      | s-src≡ , s-tgt≡ | t-src≡ , t-tgt≡ =
    μ′ , mode′ , seal★′ ,
    (subst
      (λ X → μ′ ∣ applyTyCtxs χs Δ ∣ applyStores χs Σ′
        ⊢ applyCoercions χs s ∶ applyTys χs A =⇒ X)
      s-tgt≡ s′⊢ , s′ʷ) ,
    (subst
      (λ X → μ′ ∣ applyTyCtxs χs Δ ∣ applyStores χs Σ′
        ⊢ applyCoercions χs t ∶ X =⇒ applyTys χs C)
      t-src≡ t′⊢ , t′ʷ)

  apply-fixed-widen-sequence-components :
    ∀ {χs μ Δ Σ Σ′ s t A B C} →
    StoreIncl Σ Σ′ →
    ModeRename suc μ μ →
    μ ∣ Δ ∣ Σ ⊢ s ∶ A =⇒ B →
    μ ∣ Δ ∣ Σ ⊢ t ∶ B =⇒ C →
    Widening (s ︔ t) →
    (μ ∣ applyTyCtxs χs Δ ∣ applyStores χs Σ′
      ⊢ applyCoercions χs s ∶ applyTys χs A ⊑ applyTys χs B) ×
    (μ ∣ applyTyCtxs χs Δ ∣ applyStores χs Σ′
      ⊢ applyCoercions χs t ∶ applyTys χs B ⊑ applyTys χs C)
  apply-fixed-widen-sequence-components
      {χs = χs} incl mode-rename s⊢ t⊢ sequence-widening
      with split-widening-sequence sequence-widening
  apply-fixed-widen-sequence-components
      {χs = χs} incl mode-rename s⊢ t⊢ sequence-widening
      | sʷ , tʷ =
    apply-fixed-widens-typing {χs = χs} mode-rename
      (widen-weaken ≤-refl incl (s⊢ , sʷ)) ,
    apply-fixed-widens-typing {χs = χs} mode-rename
      (widen-weaken ≤-refl incl (t⊢ , tʷ))

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

  final-narrow-component :
    ∀ {Φ Δᴸ Δᴿ V M′ A B}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      (result : WeakOneStepResult ρ V M′ A B keep)
      {μ C D c} →
    μ ∣ applyTyCtxs (targetTailChanges result) Δᴿ
      ∣ applyStores (targetTailChanges result) (rightStoreⁱ ρ)
      ⊢ applyCoercions (targetTailChanges result) c
        ∶ applyTys (targetTailChanges result) C
          ⊒ applyTys (targetTailChanges result) D →
    μ ∣ resultRightCtx result ∣ rightStoreⁱ (resultStore result)
      ⊢ applyCoercions (targetTailChanges result) c
        ∶ applyTys (targetTailChanges result) C
          ⊒ applyTys (targetTailChanges result) D
  final-narrow-component result c⊒ =
    subst
      (λ Δ → _ ∣ Δ ∣ rightStoreⁱ (resultStore result)
        ⊢ applyCoercions (targetTailChanges result) _
          ∶ applyTys (targetTailChanges result) _
            ⊒ applyTys (targetTailChanges result) _)
      (sym (targetCtxResult result))
      (subst
        (λ Σ → _ ∣ applyTyCtxs (targetTailChanges result) _ ∣ Σ
          ⊢ applyCoercions (targetTailChanges result) _
            ∶ applyTys (targetTailChanges result) _
              ⊒ applyTys (targetTailChanges result) _)
        (sym (targetStoreResult result)) c⊒)

  final-widen-component :
    ∀ {Φ Δᴸ Δᴿ V M′ A B}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      (result : WeakOneStepResult ρ V M′ A B keep)
      {μ C D c} →
    μ ∣ applyTyCtxs (targetTailChanges result) Δᴿ
      ∣ applyStores (targetTailChanges result) (rightStoreⁱ ρ)
      ⊢ applyCoercions (targetTailChanges result) c
        ∶ applyTys (targetTailChanges result) C
          ⊑ applyTys (targetTailChanges result) D →
    μ ∣ resultRightCtx result ∣ rightStoreⁱ (resultStore result)
      ⊢ applyCoercions (targetTailChanges result) c
        ∶ applyTys (targetTailChanges result) C
          ⊑ applyTys (targetTailChanges result) D
  final-widen-component result c⊑ =
    subst
      (λ Δ → _ ∣ Δ ∣ rightStoreⁱ (resultStore result)
        ⊢ applyCoercions (targetTailChanges result) _
          ∶ applyTys (targetTailChanges result) _
            ⊑ applyTys (targetTailChanges result) _)
      (sym (targetCtxResult result))
      (subst
        (λ Σ → _ ∣ applyTyCtxs (targetTailChanges result) _ ∣ Σ
          ⊢ applyCoercions (targetTailChanges result) _
            ∶ applyTys (targetTailChanges result) _
              ⊑ applyTys (targetTailChanges result) _)
        (sym (targetStoreResult result)) c⊑)

  narrow-sequence-resume :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
      {V M′ : Term} {A B C D : Ty} {s t : Coercion} {μ : ModeEnv}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
      {r : Φ ∣ Δᴸ ⊢ A ⊑ C ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ A ⊑ D ⊣ Δᴿ} →
    WorldCoherentRightTargetPendingSequenceContinuation →
    StoreImpPrefix ρ₀ ρ⁺ →
    CastMode μ →
    SealModeStore★ μ (rightStoreⁱ ρ₀) →
    μ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ s ∶ B =⇒ C →
    μ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ t ∶ C =⇒ D →
    Narrowing (s ︔ t) →
    WorldCoherentRightValueCatchupIndexedResult
      {V = V} {M′ = M′} {ρ = ρ⁺} p →
    WorldCoherentRightValueCatchupIndexedResult
      {V = V} {M′ = M′ ⟨ s ︔ t ⟩} {ρ = ρ⁺} q
  narrow-sequence-resume {A = A} {p = p} {r = r} {q = q}
      pending prefix mode seal★ s₀⊢ t₀⊢ sequence-narrowing₀
      caught@(world-coherent-right-value-indexed-catchup
        (right-value-indexed-catchup indexed refl refl
          vV noV vW noW)
        lineage bullet final-world final-exclusive final-unique final-wfR)
      with apply-narrow-sequence-components
        { χs = keep ∷ targetTailChanges (weakIndexedResult indexed) }
        (rightStoreⁱ-prefix-inclusion prefix)
        mode
        (seal★-weaken (rightStoreⁱ-prefix-inclusion prefix) seal★)
        s₀⊢ t₀⊢ sequence-narrowing₀
  narrow-sequence-resume {A = A} {p = p} {r = r} {q = q}
      pending prefix mode seal★ s₀⊢ t₀⊢ sequence-narrowing₀
      caught@(world-coherent-right-value-indexed-catchup
        (right-value-indexed-catchup indexed refl refl
          vV noV vW noW)
        lineage bullet final-world final-exclusive final-unique final-wfR)
      | μ′ , mode′ , seal★′ , s⊒′ , t⊒′
      with final-narrow-component (weakIndexedResult indexed) s⊒′
         | final-narrow-component (weakIndexedResult indexed) t⊒′
  narrow-sequence-resume {A = A} {p = p} {r = r} {q = q}
      pending prefix mode seal★ s₀⊢ t₀⊢ sequence-narrowing₀
      caught@(world-coherent-right-value-indexed-catchup
        (right-value-indexed-catchup indexed refl refl
          vV noV vW noW)
        lineage bullet final-world final-exclusive final-unique final-wfR)
      | μ′ , mode′ , seal★′ , s⊒′ , t⊒′
      | s⊒@(s⊢ , sⁿ) | t⊒@(t⊢ , tⁿ)
      with targetNarrowingAdministrationPlan
        target-administration-plan-synthesisᵀ
        { ρ₀ = resultStore (weakIndexedResult indexed) }
        { ρ⁺ = resultStore (weakIndexedResult indexed) }
        { A = A }
        { p = transportType (weakIndexedResult indexed) p }
        { q = transportType (weakIndexedResult indexed) r }
        prefix-reflⁱ final-wfR
        (final-seal-mode (weakIndexedResult indexed) seal★′)
        (s⊢ , sⁿ)
  narrow-sequence-resume {A = A} {p = p} {r = r} {q = q}
      pending prefix mode seal★ s₀⊢ t₀⊢ sequence-narrowing₀
      caught@(world-coherent-right-value-indexed-catchup
        (right-value-indexed-catchup indexed refl refl
          vV noV vW noW)
        lineage bullet final-world final-exclusive final-unique final-wfR)
      | μ′ , mode′ , seal★′ , s⊒′ , t⊒′
      | s⊒@(s⊢ , sⁿ) | t⊒@(t⊢ , tⁿ) | s-plan
      with targetNarrowingAdministrationPlan
        target-administration-plan-synthesisᵀ
        { ρ₀ = resultStore (weakIndexedResult indexed) }
        { ρ⁺ = resultStore (weakIndexedResult indexed) }
        { A = A }
        { p = transportType (weakIndexedResult indexed) r }
        { q = transportType (weakIndexedResult indexed) q }
        prefix-reflⁱ final-wfR
        (final-seal-mode (weakIndexedResult indexed) seal★′)
        (t⊢ , tⁿ)
  narrow-sequence-resume {A = A} {p = p} {r = r} {q = q}
      pending prefix mode seal★ s₀⊢ t₀⊢ sequence-narrowing₀
      caught@(world-coherent-right-value-indexed-catchup
        (right-value-indexed-catchup indexed refl refl
          vV noV vW noW)
        lineage bullet final-world final-exclusive final-unique final-wfR)
      | μ′ , mode′ , seal★′ , s⊒′ , t⊒′
      | s⊒@(s⊢ , sⁿ) | t⊒@(t⊢ , tⁿ)
      | s-plan | t-plan =
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
        final-world final-exclusive final-unique final-wfR
        (ok-no (no•-⟨⟩ (no•-⟨⟩ noW)))
        vV noV noW

  widen-sequence-resume :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
      {V M′ : Term} {A B C D : Ty} {s t : Coercion} {μ : ModeEnv}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
      {r : Φ ∣ Δᴸ ⊢ A ⊑ C ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ A ⊑ D ⊣ Δᴿ} →
    WorldCoherentRightTargetPendingSequenceContinuation →
    StoreImpPrefix ρ₀ ρ⁺ →
    CastMode μ →
    SealModeStore★ μ (rightStoreⁱ ρ₀) →
    μ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ s ∶ B =⇒ C →
    μ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ t ∶ C =⇒ D →
    Widening (s ︔ t) →
    WorldCoherentRightValueCatchupIndexedResult
      {V = V} {M′ = M′} {ρ = ρ⁺} p →
    WorldCoherentRightValueCatchupIndexedResult
      {V = V} {M′ = M′ ⟨ s ︔ t ⟩} {ρ = ρ⁺} q
  widen-sequence-resume {A = A} {p = p} {r = r} {q = q}
      pending prefix mode seal★ s₀⊢ t₀⊢ sequence-widening₀
      caught@(world-coherent-right-value-indexed-catchup
        (right-value-indexed-catchup indexed refl refl
          vV noV vW noW)
        lineage bullet final-world final-exclusive final-unique final-wfR)
      with apply-widen-sequence-components
        { χs = keep ∷ targetTailChanges (weakIndexedResult indexed) }
        (rightStoreⁱ-prefix-inclusion prefix)
        mode
        (seal★-weaken (rightStoreⁱ-prefix-inclusion prefix) seal★)
        s₀⊢ t₀⊢ sequence-widening₀
  widen-sequence-resume {A = A} {p = p} {r = r} {q = q}
      pending prefix mode seal★ s₀⊢ t₀⊢ sequence-widening₀
      caught@(world-coherent-right-value-indexed-catchup
        (right-value-indexed-catchup indexed refl refl
          vV noV vW noW)
        lineage bullet final-world final-exclusive final-unique final-wfR)
      | μ′ , mode′ , seal★′ , s⊑′ , t⊑′
      with final-widen-component (weakIndexedResult indexed) s⊑′
         | final-widen-component (weakIndexedResult indexed) t⊑′
  widen-sequence-resume {A = A} {p = p} {r = r} {q = q}
      pending prefix mode seal★ s₀⊢ t₀⊢ sequence-widening₀
      caught@(world-coherent-right-value-indexed-catchup
        (right-value-indexed-catchup indexed refl refl
          vV noV vW noW)
        lineage bullet final-world final-exclusive final-unique final-wfR)
      | μ′ , mode′ , seal★′ , s⊑′ , t⊑′
      | s⊑@(s⊢ , sʷ) | t⊑@(t⊢ , tʷ)
      with targetWideningAdministrationPlan
        target-administration-plan-synthesisᵀ
        { ρ₀ = resultStore (weakIndexedResult indexed) }
        { ρ⁺ = resultStore (weakIndexedResult indexed) }
        { A = A }
        { p = transportType (weakIndexedResult indexed) p }
        { q = transportType (weakIndexedResult indexed) r }
        prefix-reflⁱ final-wfR
        (final-seal-mode (weakIndexedResult indexed) seal★′)
        (s⊢ , sʷ)
  widen-sequence-resume {A = A} {p = p} {r = r} {q = q}
      pending prefix mode seal★ s₀⊢ t₀⊢ sequence-widening₀
      caught@(world-coherent-right-value-indexed-catchup
        (right-value-indexed-catchup indexed refl refl
          vV noV vW noW)
        lineage bullet final-world final-exclusive final-unique final-wfR)
      | μ′ , mode′ , seal★′ , s⊑′ , t⊑′
      | s⊑@(s⊢ , sʷ) | t⊑@(t⊢ , tʷ) | s-plan
      with targetWideningAdministrationPlan
        target-administration-plan-synthesisᵀ
        { ρ₀ = resultStore (weakIndexedResult indexed) }
        { ρ⁺ = resultStore (weakIndexedResult indexed) }
        { A = A }
        { p = transportType (weakIndexedResult indexed) r }
        { q = transportType (weakIndexedResult indexed) q }
        prefix-reflⁱ final-wfR
        (final-seal-mode (weakIndexedResult indexed) seal★′)
        (t⊢ , tʷ)
  widen-sequence-resume {A = A} {p = p} {r = r} {q = q}
      pending prefix mode seal★ s₀⊢ t₀⊢ sequence-widening₀
      caught@(world-coherent-right-value-indexed-catchup
        (right-value-indexed-catchup indexed refl refl
          vV noV vW noW)
        lineage bullet final-world final-exclusive final-unique final-wfR)
      | μ′ , mode′ , seal★′ , s⊑′ , t⊑′
      | s⊑@(s⊢ , sʷ) | t⊑@(t⊢ , tʷ)
      | s-plan | t-plan =
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
        final-world final-exclusive final-unique final-wfR
        (ok-no (no•-⟨⟩ (no•-⟨⟩ noW)))
        vV noV noW

  id-widen-sequence-resume :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
      {V M′ : Term} {A B C D : Ty} {s t : Coercion}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
      {r : Φ ∣ Δᴸ ⊢ A ⊑ C ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ A ⊑ D ⊣ Δᴿ} →
    WorldCoherentRightTargetPendingSequenceContinuation →
    StoreImpPrefix ρ₀ ρ⁺ →
    SealModeStore★ id-onlyᵈ (rightStoreⁱ ρ₀) →
    id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ s ∶ B =⇒ C →
    id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ t ∶ C =⇒ D →
    Widening (s ︔ t) →
    WorldCoherentRightValueCatchupIndexedResult
      {V = V} {M′ = M′} {ρ = ρ⁺} p →
    WorldCoherentRightValueCatchupIndexedResult
      {V = V} {M′ = M′ ⟨ s ︔ t ⟩} {ρ = ρ⁺} q
  id-widen-sequence-resume {A = A} {p = p} {r = r} {q = q}
      pending prefix seal★ s₀⊢ t₀⊢ sequence-widening₀
      caught@(world-coherent-right-value-indexed-catchup
        (right-value-indexed-catchup indexed refl refl
          vV noV vW noW)
        lineage bullet final-world final-exclusive final-unique final-wfR)
      with apply-fixed-widen-sequence-components
        { χs = keep ∷
          targetTailChanges (weakIndexedResult indexed) }
        (rightStoreⁱ-prefix-inclusion prefix)
        (modeRename-id-only suc)
        s₀⊢ t₀⊢ sequence-widening₀
  id-widen-sequence-resume {A = A} {p = p} {r = r} {q = q}
      pending prefix seal★ s₀⊢ t₀⊢ sequence-widening₀
      caught@(world-coherent-right-value-indexed-catchup
        (right-value-indexed-catchup indexed refl refl
          vV noV vW noW)
        lineage bullet final-world final-exclusive final-unique final-wfR)
      | s⊑′ , t⊑′
      with final-widen-component (weakIndexedResult indexed) s⊑′
         | final-widen-component (weakIndexedResult indexed) t⊑′
  id-widen-sequence-resume {A = A} {p = p} {r = r} {q = q}
      pending prefix seal★ s₀⊢ t₀⊢ sequence-widening₀
      caught@(world-coherent-right-value-indexed-catchup
        (right-value-indexed-catchup indexed refl refl
          vV noV vW noW)
        lineage bullet final-world final-exclusive final-unique final-wfR)
      | s⊑′ , t⊑′
      | s⊑@(s⊢ , sʷ) | t⊑@(t⊢ , tʷ)
      with targetWideningAdministrationPlan
        target-administration-plan-synthesisᵀ
        { ρ₀ = resultStore (weakIndexedResult indexed) }
        { ρ⁺ = resultStore (weakIndexedResult indexed) }
        { A = A }
        { p = transportType (weakIndexedResult indexed) p }
        { q = transportType (weakIndexedResult indexed) r }
        prefix-reflⁱ final-wfR seal★-id-only (s⊢ , sʷ)
  id-widen-sequence-resume {A = A} {p = p} {r = r} {q = q}
      pending prefix seal★ s₀⊢ t₀⊢ sequence-widening₀
      caught@(world-coherent-right-value-indexed-catchup
        (right-value-indexed-catchup indexed refl refl
          vV noV vW noW)
        lineage bullet final-world final-exclusive final-unique final-wfR)
      | s⊑′ , t⊑′
      | s⊑@(s⊢ , sʷ) | t⊑@(t⊢ , tʷ) | s-plan
      with targetWideningAdministrationPlan
        target-administration-plan-synthesisᵀ
        { ρ₀ = resultStore (weakIndexedResult indexed) }
        { ρ⁺ = resultStore (weakIndexedResult indexed) }
        { A = A }
        { p = transportType (weakIndexedResult indexed) r }
        { q = transportType (weakIndexedResult indexed) q }
        prefix-reflⁱ final-wfR seal★-id-only (t⊢ , tʷ)
  id-widen-sequence-resume {A = A} {p = p} {r = r} {q = q}
      pending prefix seal★ s₀⊢ t₀⊢ sequence-widening₀
      caught@(world-coherent-right-value-indexed-catchup
        (right-value-indexed-catchup indexed refl refl
          vV noV vW noW)
        lineage bullet final-world final-exclusive final-unique final-wfR)
      | s⊑′ , t⊑′
      | s⊑@(s⊢ , sʷ) | t⊑@(t⊢ , tʷ)
      | s-plan | t-plan =
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
        final-world final-exclusive final-unique final-wfR
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
    AssumptionMembershipUnique Φ →
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
  narrow-administration inert pending roots prefix coherent exclusive unique wfR
      runtime vV noV mode seal★ c⊒ relation caught (plan-inert c-inert) =
    inert prefix c-inert
      (inj₂ (inj₂ (inj₁ (_ , mode , seal★ , c⊒)))) caught
  narrow-administration inert pending roots prefix coherent exclusive unique wfR
      runtime vV noV mode seal★ c⊒ relation caught plan-id =
    rightTargetNarrowIdentityRoot roots prefix coherent exclusive unique wfR
      runtime vV noV mode seal★ c⊒ relation caught
  narrow-administration inert pending roots prefix coherent exclusive unique wfR
      runtime vV noV mode seal★ c⊒ relation caught plan-untag =
    rightTargetNarrowUntagRoot roots prefix coherent exclusive unique wfR
      runtime vV noV mode seal★ c⊒ relation caught
  narrow-administration inert pending roots prefix coherent exclusive unique wfR
      runtime vV noV mode seal★ c⊒ relation caught
      plan-fun-untag-gen =
    rightTargetNarrowFunUntagGenRoot roots prefix coherent exclusive unique wfR
      runtime vV noV mode seal★ c⊒ relation caught
  narrow-administration inert pending roots prefix coherent exclusive unique wfR
      runtime vV noV mode seal★
      (C.cast-seq (C.cast-inst hFun occ s⊢)
        (C.cast-tag hG gG tag-ok) , NW.cross ())
      relation caught plan-inst-fun-tag
  narrow-administration inert pending roots prefix coherent exclusive unique wfR
      runtime vV noV mode seal★
      (C.cast-unseal hB αB∈Σ ok , NW.cross ())
      relation caught plan-unseal
  narrow-administration inert pending roots prefix coherent exclusive unique wfR
      runtime vV noV mode seal★
      (C.cast-inst hB occ s⊢ , NW.cross ()) relation caught plan-inst
  narrow-administration inert pending roots prefix coherent exclusive unique wfR
      runtime vV noV mode seal★
      (C.cast-seq s⊢ t⊢ , sequence-narrowing) relation caught
      (plan-seq {r = r} s-plan t-plan) =
    narrow-sequence-resume {r = r} pending prefix mode seal★
      s⊢ t⊢ sequence-narrowing caught

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
    AssumptionMembershipUnique Φ →
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
      exclusive unique wfR runtime vV noV mode seal★ c⊑ relation caught
      (plan-inert c-inert) =
    inert prefix c-inert
      (inj₂ (inj₂ (inj₂
        (inj₁ (_ , mode , seal★ , c⊑))))) caught
  widen-administration inert pending roots allocation prefix coherent
      exclusive unique wfR runtime vV noV mode seal★ c⊑ relation caught
      plan-id =
    rightTargetWidenIdentityRoot roots prefix coherent exclusive unique wfR
      runtime vV noV mode seal★ c⊑ relation caught
  widen-administration inert pending roots allocation prefix coherent
      exclusive unique wfR runtime vV noV mode seal★
      (C.cast-untag hH gH ok , NW.cross ()) relation caught plan-untag
  widen-administration inert pending roots allocation prefix coherent
      exclusive unique wfR runtime vV noV mode seal★ c⊑ relation caught
      plan-unseal =
    rightTargetWidenUnsealRoot roots prefix coherent exclusive unique wfR
      runtime vV noV mode seal★ c⊑ relation caught
  widen-administration inert pending roots allocation prefix coherent
      exclusive unique wfR runtime vV noV mode seal★ c⊑ relation caught
      plan-inst =
    rightTargetWidenInstantiationRoot roots allocation prefix coherent
      exclusive unique wfR runtime vV noV mode seal★ c⊑ relation caught
  widen-administration inert pending roots allocation prefix coherent
      exclusive unique wfR runtime vV noV mode seal★ c⊑ relation caught
      plan-inst-fun-tag =
    rightTargetWidenInstFunTagRoot roots allocation prefix coherent
      exclusive unique wfR runtime vV noV mode seal★ c⊑ relation caught
  widen-administration inert pending roots allocation prefix coherent
      exclusive unique wfR runtime vV noV mode seal★
      (C.cast-seq (C.cast-untag hG gG tag-ok)
        (C.cast-gen hFun occ s⊢) , NW.cross ())
      relation caught plan-fun-untag-gen
  widen-administration inert pending roots allocation prefix coherent
      exclusive unique wfR runtime vV noV mode seal★
      (C.cast-seq s⊢ t⊢ , sequence-widening) relation caught
      (plan-seq {r = r} s-plan t-plan) =
    widen-sequence-resume {r = r} pending prefix mode seal★
      s⊢ t⊢ sequence-widening caught

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
    AssumptionMembershipUnique Φ →
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
      exclusive unique wfR runtime vV noV seal★ c⊑ relation caught
      (plan-inert c-inert) =
    inert prefix c-inert
      (inj₂ (inj₂ (inj₂ (inj₂ (seal★ , c⊑))))) caught
  id-widen-administration inert pending roots allocation prefix coherent
      exclusive unique wfR runtime vV noV seal★ c⊑ relation caught plan-id =
    rightTargetIdWidenIdentityRoot roots prefix coherent exclusive unique wfR
      runtime vV noV seal★ c⊑ relation caught
  id-widen-administration inert pending roots allocation prefix coherent
      exclusive unique wfR runtime vV noV seal★
      (C.cast-untag hH gH ok , NW.cross ()) relation caught plan-untag
  id-widen-administration inert pending roots allocation prefix coherent
      exclusive unique wfR runtime vV noV seal★
      (C.cast-unseal hB αB∈Σ () , cʷ) relation caught plan-unseal
  id-widen-administration inert pending roots allocation prefix coherent
      exclusive unique wfR runtime vV noV seal★ c⊑ relation caught
      plan-inst =
    rightTargetWidenInstantiationRoot roots allocation prefix coherent
      exclusive unique wfR runtime vV noV cast-tag-or-id seal★-tag-or-id
      (NW.widen-mode-relax C.id-only≤tag-or-idᵈ c⊑)
      relation caught
  id-widen-administration inert pending roots allocation prefix coherent
      exclusive unique wfR runtime vV noV seal★ c⊑ relation caught
      plan-inst-fun-tag =
    rightTargetWidenInstFunTagRoot roots allocation prefix coherent
      exclusive unique wfR runtime vV noV cast-tag-or-id seal★-tag-or-id
      (NW.widen-mode-relax C.id-only≤tag-or-idᵈ c⊑)
      relation caught
  id-widen-administration inert pending roots allocation prefix coherent
      exclusive unique wfR runtime vV noV seal★
      (C.cast-seq (C.cast-untag hG gG tag-ok)
        (C.cast-gen hFun occ s⊢) , NW.cross ())
      relation caught plan-fun-untag-gen
  id-widen-administration inert pending roots allocation prefix coherent
      exclusive unique wfR runtime vV noV seal★
      (C.cast-seq s⊢ t⊢ , sequence-widening) relation caught
      (plan-seq {r = r} s-plan t-plan) =
    id-widen-sequence-resume {r = r} pending prefix seal★
      s⊢ t⊢ sequence-widening caught

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
    AssumptionMembershipUnique Φ →
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
  reveal-administration inert roots prefix coherent exclusive unique wfR runtime
      vV noV c↑@(reveal-id-var hY ok) relation caught =
    rightTargetRevealIdentityRoot roots prefix coherent exclusive unique wfR
      runtime vV noV c↑ relation caught
  reveal-administration inert roots prefix coherent exclusive unique wfR runtime
      vV noV c↑@reveal-id-base relation caught =
    rightTargetRevealIdentityRoot roots prefix coherent exclusive unique wfR
      runtime vV noV c↑ relation caught
  reveal-administration inert roots prefix coherent exclusive unique wfR runtime
      vV noV c↑@reveal-id-★ relation caught =
    rightTargetRevealIdentityRoot roots prefix coherent exclusive unique wfR
      runtime vV noV c↑ relation caught
  reveal-administration inert roots prefix coherent exclusive unique wfR runtime
      vV noV c↑@(reveal-unseal hC α∈Σ ok) relation caught =
    rightTargetRevealUnsealRoot roots prefix coherent exclusive unique wfR
      runtime vV noV c↑ relation caught
  reveal-administration inert roots prefix coherent exclusive unique wfR runtime
      vV noV c↑@(reveal-fun {s = s} {t = t} s↓ t↑)
      relation caught =
    inert prefix (s C.↦ t) (inj₁ (_ , _ , _ , c↑)) caught
  reveal-administration inert roots prefix coherent exclusive unique wfR runtime
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
    AssumptionMembershipUnique Φ →
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
  conceal-administration inert roots prefix coherent
      exclusive unique wfR runtime vV noV
      c↓@(conceal-id-var hY ok) relation caught =
    rightTargetConcealIdentityRoot roots prefix coherent exclusive unique wfR
      runtime vV noV c↓ relation caught
  conceal-administration inert roots prefix coherent
      exclusive unique wfR runtime vV noV
      c↓@conceal-id-base relation caught =
    rightTargetConcealIdentityRoot roots prefix coherent exclusive unique wfR
      runtime vV noV c↓ relation caught
  conceal-administration inert roots prefix coherent
      exclusive unique wfR runtime vV noV
      c↓@conceal-id-★ relation caught =
    rightTargetConcealIdentityRoot roots prefix coherent exclusive unique wfR
      runtime vV noV c↓ relation caught
  conceal-administration { β = β } {X = X}
      inert roots prefix coherent exclusive unique wfR runtime vV noV
      c↓@(conceal-seal hX β∈Σ ok) relation caught =
    inert prefix (C.seal X β)
      (inj₂ (inj₁ (_ , _ , _ , c↓))) caught
  conceal-administration inert roots prefix coherent
      exclusive unique wfR runtime vV noV
      c↓@(conceal-fun {s = s} {t = t} s↑ t↓)
      relation caught =
    inert prefix (s C.↦ t)
      (inj₂ (inj₁ (_ , _ , _ , c↓))) caught
  conceal-administration inert roots prefix coherent
      exclusive unique wfR runtime vV noV
      c↓@(conceal-all {s = s} s↓) relation caught =
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
        λ prefix coherent exclusive unique wfR runtime vV noV mode seal★ c⊒
          relation caught →
        narrow-administration inert pending roots prefix coherent
          exclusive unique wfR runtime vV noV mode seal★ c⊒ relation caught
          (targetNarrowingAdministrationPlan
            target-administration-plan-synthesisᵀ
            prefix wfR seal★ c⊒)
    ; rightTargetWidenFrame =
        λ prefix coherent exclusive unique wfR runtime vV noV mode seal★ c⊑
          relation caught →
        widen-administration inert pending roots allocation prefix coherent
          exclusive unique wfR runtime vV noV mode seal★ c⊑ relation caught
          (targetWideningAdministrationPlan
            target-administration-plan-synthesisᵀ
            prefix wfR seal★ c⊑)
    ; rightTargetIdWidenFrame =
        λ prefix coherent exclusive unique wfR runtime vV noV seal★ c⊑
          relation caught →
        id-widen-administration inert pending roots allocation prefix
          coherent exclusive unique wfR runtime vV noV seal★ c⊑
          relation caught
          (targetWideningAdministrationPlan
            target-administration-plan-synthesisᵀ
            prefix wfR seal★ c⊑)
    ; rightTargetRevealFrame =
        λ prefix coherent exclusive unique wfR runtime vV noV
          c↑ relation caught →
        reveal-administration inert roots prefix coherent exclusive unique wfR
          runtime vV noV c↑ relation caught
    ; rightTargetConcealFrame =
        λ prefix coherent exclusive unique wfR runtime vV noV
          c↓ relation caught →
        conceal-administration inert roots prefix coherent exclusive unique wfR
          runtime vV noV c↓ relation caught
    }

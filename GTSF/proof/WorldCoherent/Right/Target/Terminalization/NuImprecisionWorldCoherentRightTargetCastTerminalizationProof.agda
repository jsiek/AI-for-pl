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
--   * Transports stored component cast shapes and exact triangles through
--     target catch-up before re-synthesizing the component plans.
--   * Contains no result, outcome, view, alias, postulate, hole, permissive
--     option, compatibility wrapper, or termination bypass.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc)
open import Data.Nat.Properties using (≤-refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import Coercions as C
open import CastImprecisionShape using
  (narrowing; widening; _⊢ᶜ_⦂_)
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
open import ConversionIndexCompatibility using (_[_↦_]ᴿ_)
open import ImprecisionComposition using
  (ImprecisionShape; ⌊_⌋; _；_≋_)
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
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; rightStoreⁱ
  )
open import proof.Core.Properties.CastImprecision using
  ( seal★-tag-or-id
  )
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
  (seal★-id-only)
open import proof.Core.Properties.NuNarrowingTransport using
  (apply-narrows-typing)
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  (rightStoreⁱ-prefix-inclusion)
open import proof.Core.Administration.NuImprecisionAdministrationMeasureProof using
  (sequence-rank-decreases)
open import proof.Target.Administration.NuImprecisionTargetAdministrationPlanDef using
  ( TargetAdministrationPlan
  ; plan-fun-untag-gen
  ; plan-id
  ; plan-inert
  ; plan-inst
  ; plan-inst-fun-tag
  ; plan-narrow-seq
  ; plan-widen-seq
  ; plan-id-widen-seq
  ; plan-unseal
  ; plan-untag
  )
open import proof.Target.Administration.NuImprecisionTargetAdministrationPlanSynthesisDef using
  ( targetNarrowingAdministrationPlan
  ; targetWideningAdministrationPlan
  ; targetIdWideningAdministrationPlan
  )
open import proof.Target.Administration.NuImprecisionTargetAdministrationPlanSynthesisLemma using
  (target-administration-plan-synthesisᵀ)
open import
  proof.Target.Administration.NuImprecisionTargetFusedAdministrationPlanDecomposition
  using
  ( target-fun-untag-gen-plan-decompositionᵀ
  ; target-inst-fun-tag-plan-decompositionᵀ
  )
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
  ; transportShapeCoherent
  ; transportType
  ; weakIndexedResult
  ; weakIndexedTypeCoherence
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
open import proof.Core.Properties.NuCastImprecisionShapeProperties using
  ( cast-shape-applyCoercions
  ; imprecision-composition-shape-transport
  )
open import proof.Core.Properties.TypePreservation using (seal★-weaken)


private

  map-fifth-alternative :
    ∀ {A B C D E F : Set} →
    (E → F) →
    A ⊎ B ⊎ C ⊎ D ⊎ E →
    A ⊎ B ⊎ C ⊎ D ⊎ F
  map-fifth-alternative convert (inj₁ first) =
    inj₁ first
  map-fifth-alternative convert (inj₂ (inj₁ second)) =
    inj₂ (inj₁ second)
  map-fifth-alternative convert (inj₂ (inj₂ (inj₁ third))) =
    inj₂ (inj₂ (inj₁ third))
  map-fifth-alternative convert
      (inj₂ (inj₂ (inj₂ (inj₁ fourth)))) =
    inj₂ (inj₂ (inj₂ (inj₁ fourth)))
  map-fifth-alternative convert
      (inj₂ (inj₂ (inj₂ (inj₂ fifth)))) =
    inj₂ (inj₂ (inj₂ (inj₂ (convert fifth))))

  narrowing-widening-sequence⊥ :
    ∀ {s t} → Narrowing (s ︔ t) → Widening (s ︔ t) → ⊥
  narrowing-widening-sequence⊥ (gG NW.？︔ gⁿ) (NW.cross ())
  narrowing-widening-sequence⊥ (gG NW.？︔ gⁿ) (() NW.︔ gH !)
  narrowing-widening-sequence⊥
    (NW.fun-untag-gen safe) (NW.cross ())
  narrowing-widening-sequence⊥
    (sⁿ NW.︔seal α) (NW.cross ())
  narrowing-widening-sequence⊥
    ((NW.strict-crossⁿ ()) NW.︔seal α)
    (NW.unseal︔_ β tʷ)

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
      {q : Φ ∣ Δᴸ ⊢ A ⊑ D ⊣ Δᴿ}
      {s-shape t-shape : ImprecisionShape} →
    WorldCoherentRightTargetPendingSequenceContinuation →
    StoreImpPrefix ρ₀ ρ⁺ →
    CastMode μ →
    SealModeStore★ μ (rightStoreⁱ ρ₀) →
    μ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ s ∶ B =⇒ C →
    μ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ t ∶ C =⇒ D →
    Narrowing (s ︔ t) →
    narrowing ⊢ᶜ s ⦂ s-shape →
    ⌊ r ⌋ ； s-shape ≋ ⌊ p ⌋ →
    narrowing ⊢ᶜ t ⦂ t-shape →
    ⌊ q ⌋ ； t-shape ≋ ⌊ r ⌋ →
    WorldCoherentRightValueCatchupIndexedResult
      {V = V} {M′ = M′} {ρ = ρ⁺} p →
    WorldCoherentRightValueCatchupIndexedResult
      {V = V} {M′ = M′ ⟨ s ︔ t ⟩} {ρ = ρ⁺} q
  narrow-sequence-resume {A = A} {p = p} {r = r} {q = q}
      pending prefix mode seal★ s₀⊢ t₀⊢ sequence-narrowing₀
      s-shape s-comp t-shape t-comp
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
      s-shape s-comp t-shape t-comp
      caught@(world-coherent-right-value-indexed-catchup
        (right-value-indexed-catchup indexed refl refl
          vV noV vW noW)
        lineage bullet final-world final-exclusive final-unique final-wfR)
      | μ′ , mode′ , seal★′ , s⊒′ , t⊒′
      with final-narrow-component (weakIndexedResult indexed) s⊒′
         | final-narrow-component (weakIndexedResult indexed) t⊒′
  narrow-sequence-resume {A = A} {p = p} {r = r} {q = q}
      pending prefix mode seal★ s₀⊢ t₀⊢ sequence-narrowing₀
      s-shape s-comp t-shape t-comp
      caught@(world-coherent-right-value-indexed-catchup
        (right-value-indexed-catchup indexed refl refl
          vV noV vW noW)
        lineage bullet final-world final-exclusive final-unique final-wfR)
      | μ′ , mode′ , seal★′ , s⊒′ , t⊒′
      | s⊒@(s⊢ , sⁿ) | t⊒@(t⊢ , tⁿ)
      =
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
        (cast-shape-applyCoercions
          (targetTailChanges result) s-shape)
        (imprecision-composition-shape-transport
          (transportShapeCoherent
            (weakIndexedTypeCoherence indexed) r)
          refl
          (transportShapeCoherent
            (weakIndexedTypeCoherence indexed) p)
          s-comp)
        (cast-shape-applyCoercions
          (targetTailChanges result) t-shape)
        (imprecision-composition-shape-transport
          (transportShapeCoherent
            (weakIndexedTypeCoherence indexed) q)
          refl
          (transportShapeCoherent
            (weakIndexedTypeCoherence indexed) r)
          t-comp)
        (sequence-rank-decreases
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
      {q : Φ ∣ Δᴸ ⊢ A ⊑ D ⊣ Δᴿ}
      {s-shape t-shape : ImprecisionShape} →
    WorldCoherentRightTargetPendingSequenceContinuation →
    StoreImpPrefix ρ₀ ρ⁺ →
    CastMode μ →
    SealModeStore★ μ (rightStoreⁱ ρ₀) →
    μ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ s ∶ B =⇒ C →
    μ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ t ∶ C =⇒ D →
    Widening (s ︔ t) →
    widening ⊢ᶜ s ⦂ s-shape →
    ⌊ p ⌋ ； s-shape ≋ ⌊ r ⌋ →
    widening ⊢ᶜ t ⦂ t-shape →
    ⌊ r ⌋ ； t-shape ≋ ⌊ q ⌋ →
    WorldCoherentRightValueCatchupIndexedResult
      {V = V} {M′ = M′} {ρ = ρ⁺} p →
    WorldCoherentRightValueCatchupIndexedResult
      {V = V} {M′ = M′ ⟨ s ︔ t ⟩} {ρ = ρ⁺} q
  widen-sequence-resume {A = A} {p = p} {r = r} {q = q}
      pending prefix mode seal★ s₀⊢ t₀⊢ sequence-widening₀
      s-shape s-comp t-shape t-comp
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
      s-shape s-comp t-shape t-comp
      caught@(world-coherent-right-value-indexed-catchup
        (right-value-indexed-catchup indexed refl refl
          vV noV vW noW)
        lineage bullet final-world final-exclusive final-unique final-wfR)
      | μ′ , mode′ , seal★′ , s⊑′ , t⊑′
      with final-widen-component (weakIndexedResult indexed) s⊑′
         | final-widen-component (weakIndexedResult indexed) t⊑′
  widen-sequence-resume {A = A} {p = p} {r = r} {q = q}
      pending prefix mode seal★ s₀⊢ t₀⊢ sequence-widening₀
      s-shape s-comp t-shape t-comp
      caught@(world-coherent-right-value-indexed-catchup
        (right-value-indexed-catchup indexed refl refl
          vV noV vW noW)
        lineage bullet final-world final-exclusive final-unique final-wfR)
      | μ′ , mode′ , seal★′ , s⊑′ , t⊑′
      | s⊑@(s⊢ , sʷ) | t⊑@(t⊢ , tʷ)
      =
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
        (cast-shape-applyCoercions
          (targetTailChanges result) s-shape)
        (imprecision-composition-shape-transport
          (transportShapeCoherent
            (weakIndexedTypeCoherence indexed) p)
          refl
          (transportShapeCoherent
            (weakIndexedTypeCoherence indexed) r)
          s-comp)
        (cast-shape-applyCoercions
          (targetTailChanges result) t-shape)
        (imprecision-composition-shape-transport
          (transportShapeCoherent
            (weakIndexedTypeCoherence indexed) r)
          refl
          (transportShapeCoherent
            (weakIndexedTypeCoherence indexed) q)
          t-comp)
        (sequence-rank-decreases
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
      {q : Φ ∣ Δᴸ ⊢ A ⊑ D ⊣ Δᴿ}
      {s-shape t-shape : ImprecisionShape} →
    WorldCoherentRightTargetPendingSequenceContinuation →
    StoreImpPrefix ρ₀ ρ⁺ →
    SealModeStore★ id-onlyᵈ (rightStoreⁱ ρ₀) →
    id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ s ∶ B =⇒ C →
    id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ t ∶ C =⇒ D →
    Widening (s ︔ t) →
    widening ⊢ᶜ s ⦂ s-shape →
    ⌊ p ⌋ ； s-shape ≋ ⌊ r ⌋ →
    widening ⊢ᶜ t ⦂ t-shape →
    ⌊ r ⌋ ； t-shape ≋ ⌊ q ⌋ →
    WorldCoherentRightValueCatchupIndexedResult
      {V = V} {M′ = M′} {ρ = ρ⁺} p →
    WorldCoherentRightValueCatchupIndexedResult
      {V = V} {M′ = M′ ⟨ s ︔ t ⟩} {ρ = ρ⁺} q
  id-widen-sequence-resume {A = A} {p = p} {r = r} {q = q}
      pending prefix seal★ s₀⊢ t₀⊢ sequence-widening₀
      s-shape s-comp t-shape t-comp
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
      s-shape s-comp t-shape t-comp
      caught@(world-coherent-right-value-indexed-catchup
        (right-value-indexed-catchup indexed refl refl
          vV noV vW noW)
        lineage bullet final-world final-exclusive final-unique final-wfR)
      | s⊑′ , t⊑′
      with final-widen-component (weakIndexedResult indexed) s⊑′
         | final-widen-component (weakIndexedResult indexed) t⊑′
  id-widen-sequence-resume {A = A} {p = p} {r = r} {q = q}
      pending prefix seal★ s₀⊢ t₀⊢ sequence-widening₀
      s-shape s-comp t-shape t-comp
      caught@(world-coherent-right-value-indexed-catchup
        (right-value-indexed-catchup indexed refl refl
          vV noV vW noW)
        lineage bullet final-world final-exclusive final-unique final-wfR)
      | s⊑′ , t⊑′
      | s⊑@(s⊢ , sʷ) | t⊑@(t⊢ , tʷ)
      =
    world-coherent-right-target-sequence-resume-proofᵀ
      caught continuation
    where
    result = weakIndexedResult indexed

    continuation =
      rightTargetPendingIdWidenSequence pending
        (rightCatchupTargetValue
          (worldRightCatchupResult caught))
        seal★-id-only (s⊢ , sʷ) (t⊢ , tʷ)
        (cast-shape-applyCoercions
          (targetTailChanges result) s-shape)
        (imprecision-composition-shape-transport
          (transportShapeCoherent
            (weakIndexedTypeCoherence indexed) p)
          refl
          (transportShapeCoherent
            (weakIndexedTypeCoherence indexed) r)
          s-comp)
        (cast-shape-applyCoercions
          (targetTailChanges result) t-shape)
        (imprecision-composition-shape-transport
          (transportShapeCoherent
            (weakIndexedTypeCoherence indexed) r)
          refl
          (transportShapeCoherent
            (weakIndexedTypeCoherence indexed) q)
          t-comp)
        (sequence-rank-decreases
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
      {q : Φ ∣ Δᴸ ⊢ A ⊑ C ⊣ Δᴿ}
      {s : ImprecisionShape} →
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
    narrowing ⊢ᶜ c ⦂ s →
    ⌊ q ⌋ ； s ≋ ⌊ p ⌋ →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
      ⊢ᴺ V ⊑ M′ ⦂ A ⊑ B ∶ p →
    WorldCoherentRightValueCatchupIndexedResult
      {V = V} {M′ = M′} {ρ = ρ⁺} p →
    TargetAdministrationPlan ρ₀ A (proj₁ c⊒) p q →
    WorldCoherentRightValueCatchupIndexedResult
      {V = V} {M′ = M′ ⟨ c ⟩} {ρ = ρ⁺} q
  narrow-administration inert pending roots prefix coherent exclusive unique wfR
      runtime vV noV mode seal★ c⊒ c-shape comp relation caught
      (plan-inert c-inert stored) =
    inert prefix c-inert
      (map-fifth-alternative
        (λ { (shape , seal★′ , c⊑′ , c-shape′ , comp′) →
          seal★′ , shape , c⊑′ , c-shape′ , comp′ })
        stored)
      caught
  narrow-administration inert pending roots prefix coherent exclusive unique wfR
      runtime vV noV mode seal★ c⊒ c-shape comp relation caught
      (plan-id evidence) =
    rightTargetNarrowIdentityRoot roots prefix coherent exclusive unique wfR
      runtime vV noV mode seal★ c⊒ c-shape comp relation caught
  narrow-administration inert pending roots prefix coherent exclusive unique wfR
      runtime vV noV mode seal★ c⊒ c-shape comp relation caught
      (plan-untag mode′ seal★′ untag⊒ untag-shape untag-comp) =
    rightTargetNarrowUntagRoot roots prefix coherent exclusive unique wfR
      runtime vV noV mode seal★ c⊒ c-shape comp relation caught
  narrow-administration inert pending roots prefix coherent exclusive unique wfR
      runtime vV noV mode seal★ c⊒ c-shape comp relation caught
      plan@(plan-fun-untag-gen stored)
      with target-fun-untag-gen-plan-decompositionᵀ plan
  narrow-administration inert pending roots prefix coherent exclusive unique wfR
      runtime vV noV mode seal★ c⊒ c-shape comp relation caught
      plan@(plan-fun-untag-gen stored)
      | r ,
        untag-shape , untag-evidence , untag-comp ,
        gen-shape , gen-evidence , gen-comp ,
        untag-plan , gen-plan =
    rightTargetNarrowFunUntagGenRoot roots prefix coherent exclusive unique wfR
      runtime vV noV mode seal★ c⊒
      c-shape comp
      untag-evidence untag-comp gen-evidence gen-comp relation caught
  narrow-administration inert pending roots prefix coherent exclusive unique wfR
      runtime vV noV mode seal★
      (C.cast-seq (C.cast-inst hFun occ s⊢)
        (C.cast-tag hG gG tag-ok) , NW.cross ())
      c-shape comp relation caught (plan-inst-fun-tag stored)
  narrow-administration inert pending roots prefix coherent exclusive unique wfR
      runtime vV noV mode seal★
      (C.cast-unseal hB αB∈Σ ok , NW.cross ())
      c-shape comp relation caught (plan-unseal stored)
  narrow-administration inert pending roots prefix coherent exclusive unique wfR
      runtime vV noV mode seal★
      (C.cast-inst hB occ s⊢ , NW.cross ())
      c-shape comp relation caught (plan-inst stored)
  narrow-administration inert pending roots prefix coherent exclusive unique wfR
      runtime vV noV mode seal★
      (C.cast-seq s⊢ t⊢ , sequence-narrowing)
      c-shape comp relation caught
      (plan-narrow-seq {r = r}
        mode′ seal★′ sequence⊒
        sequence-narrowing′ sequence-shape sequence-comp
        s-shape s-comp t-shape t-comp s-plan t-plan) =
    narrow-sequence-resume {r = r} pending prefix mode seal★
      s⊢ t⊢ sequence-narrowing
      s-shape s-comp t-shape t-comp caught
  narrow-administration inert pending roots prefix coherent exclusive unique wfR
      runtime vV noV mode seal★
      (C.cast-seq s⊢ t⊢ , sequence-narrowing)
      c-shape comp relation caught
      (plan-widen-seq mode′ seal★′ sequence⊑ sequence-widening
        sequence-shape sequence-comp
        s-shape s-comp t-shape t-comp s-plan t-plan) =
    ⊥-elim
      (narrowing-widening-sequence⊥
        sequence-narrowing sequence-widening)
  narrow-administration inert pending roots prefix coherent exclusive unique wfR
      runtime vV noV mode seal★
      (C.cast-seq s⊢ t⊢ , sequence-narrowing)
      c-shape comp relation caught
      (plan-id-widen-seq seal★′ sequence⊑ sequence-widening
        sequence-shape sequence-comp
        s-shape s-comp t-shape t-comp s-plan t-plan) =
    ⊥-elim
      (narrowing-widening-sequence⊥
        sequence-narrowing sequence-widening)

  widen-administration :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
      {V M′ : Term} {A B C : Ty} {c : Coercion} {μ : ModeEnv}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ A ⊑ C ⊣ Δᴿ}
      {s : ImprecisionShape} →
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
    widening ⊢ᶜ c ⦂ s →
    ⌊ p ⌋ ； s ≋ ⌊ q ⌋ →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
      ⊢ᴺ V ⊑ M′ ⦂ A ⊑ B ∶ p →
    WorldCoherentRightValueCatchupIndexedResult
      {V = V} {M′ = M′} {ρ = ρ⁺} p →
    TargetAdministrationPlan ρ₀ A (proj₁ c⊑) p q →
    WorldCoherentRightValueCatchupIndexedResult
      {V = V} {M′ = M′ ⟨ c ⟩} {ρ = ρ⁺} q
  widen-administration inert pending roots allocation prefix coherent
      exclusive unique wfR runtime vV noV mode seal★ c⊑ c-shape comp
      relation caught
      (plan-inert c-inert stored) =
    inert prefix c-inert
      (map-fifth-alternative
        (λ { (shape , seal★′ , c⊑′ , c-shape′ , comp′) →
          seal★′ , shape , c⊑′ , c-shape′ , comp′ })
        stored)
      caught
  widen-administration inert pending roots allocation prefix coherent
      exclusive unique wfR runtime vV noV mode seal★ c⊑ c-shape comp
      relation caught
      (plan-id evidence) =
    rightTargetWidenIdentityRoot roots prefix coherent exclusive unique wfR
      runtime vV noV mode seal★ c⊑ c-shape comp relation caught
  widen-administration inert pending roots allocation prefix coherent
      exclusive unique wfR runtime vV noV mode seal★
      (C.cast-untag hH gH ok , NW.cross ())
      c-shape comp relation caught
      (plan-untag mode′ seal★′ untag⊒ untag-shape untag-comp)
  widen-administration inert pending roots allocation prefix coherent
      exclusive unique wfR runtime vV noV mode seal★ c⊑ c-shape comp
      relation caught
      (plan-unseal stored) =
    rightTargetWidenUnsealRoot roots prefix coherent exclusive unique wfR
      runtime vV noV mode seal★ c⊑ c-shape comp relation caught
  widen-administration inert pending roots allocation prefix coherent
      exclusive unique wfR runtime vV noV mode seal★ c⊑ c-shape comp
      relation caught
      (plan-inst stored) =
    rightTargetWidenInstantiationRoot roots allocation prefix coherent
      exclusive unique wfR runtime vV noV mode seal★ c⊑ c-shape comp
      relation caught
  widen-administration inert pending roots allocation prefix coherent
      exclusive unique wfR runtime vV noV mode seal★ c⊑ c-shape comp
      relation caught
      plan@(plan-inst-fun-tag stored)
      with target-inst-fun-tag-plan-decompositionᵀ plan
  widen-administration inert pending roots allocation prefix coherent
      exclusive unique wfR runtime vV noV mode seal★ c⊑ c-shape comp
      relation caught
      plan@(plan-inst-fun-tag stored)
      | r ,
        inst-shape , inst-evidence , inst-comp ,
        tag-shape , tag-evidence , tag-comp ,
        inst-plan , tag-plan =
    rightTargetWidenInstFunTagRoot roots allocation prefix coherent
      exclusive unique wfR runtime vV noV mode seal★ c⊑
      c-shape comp inst-evidence inst-comp tag-evidence tag-comp
      relation caught
  widen-administration inert pending roots allocation prefix coherent
      exclusive unique wfR runtime vV noV mode seal★
      (C.cast-seq (C.cast-untag hG gG tag-ok)
        (C.cast-gen hFun occ s⊢) , NW.cross ())
      c-shape comp relation caught (plan-fun-untag-gen stored)
  widen-administration inert pending roots allocation prefix coherent
      exclusive unique wfR runtime vV noV mode seal★
      (C.cast-seq s⊢ t⊢ , sequence-widening)
      c-shape comp relation caught
      (plan-widen-seq {r = r}
        mode′ seal★′ sequence⊑
        sequence-widening′ sequence-shape sequence-comp
        s-shape s-comp t-shape t-comp s-plan t-plan) =
    widen-sequence-resume {r = r} pending prefix mode seal★
      s⊢ t⊢ sequence-widening
      s-shape s-comp t-shape t-comp caught
  widen-administration inert pending roots allocation prefix coherent
      exclusive unique wfR runtime vV noV mode seal★
      (C.cast-seq s⊢ t⊢ , sequence-widening)
      c-shape comp relation caught
      (plan-id-widen-seq {r = r}
        seal★′ sequence⊑
        sequence-widening′ sequence-shape sequence-comp
        s-shape s-comp t-shape t-comp s-plan t-plan) =
    widen-sequence-resume {r = r} pending prefix mode seal★
      s⊢ t⊢ sequence-widening
      s-shape s-comp t-shape t-comp caught
  widen-administration inert pending roots allocation prefix coherent
      exclusive unique wfR runtime vV noV mode seal★
      (C.cast-seq s⊢ t⊢ , sequence-widening)
      c-shape comp relation caught
      (plan-narrow-seq mode′ seal★′ sequence⊒ sequence-narrowing
        sequence-shape sequence-comp
        s-shape s-comp t-shape t-comp s-plan t-plan) =
    ⊥-elim
      (narrowing-widening-sequence⊥
        sequence-narrowing sequence-widening)

  id-widen-administration :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
      {V M′ : Term} {A B C : Ty} {c : Coercion}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ A ⊑ C ⊣ Δᴿ}
      {s : ImprecisionShape} →
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
    widening ⊢ᶜ c ⦂ s →
    ⌊ p ⌋ ； s ≋ ⌊ q ⌋ →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
      ⊢ᴺ V ⊑ M′ ⦂ A ⊑ B ∶ p →
    WorldCoherentRightValueCatchupIndexedResult
      {V = V} {M′ = M′} {ρ = ρ⁺} p →
    TargetAdministrationPlan ρ₀ A (proj₁ c⊑) p q →
    WorldCoherentRightValueCatchupIndexedResult
      {V = V} {M′ = M′ ⟨ c ⟩} {ρ = ρ⁺} q
  id-widen-administration inert pending roots allocation prefix coherent
      exclusive unique wfR runtime vV noV seal★ c⊑ c-shape comp
      relation caught
      (plan-inert c-inert stored) =
    inert prefix c-inert
      (map-fifth-alternative
        (λ { (shape , seal★′ , c⊑′ , c-shape′ , comp′) →
          seal★′ , shape , c⊑′ , c-shape′ , comp′ })
        stored)
      caught
  id-widen-administration inert pending roots allocation prefix coherent
      exclusive unique wfR runtime vV noV seal★ c⊑ c-shape comp
      relation caught (plan-id evidence) =
    rightTargetIdWidenIdentityRoot roots prefix coherent exclusive unique wfR
      runtime vV noV seal★ c⊑ c-shape comp relation caught
  id-widen-administration inert pending roots allocation prefix coherent
      exclusive unique wfR runtime vV noV seal★
      (C.cast-untag hH gH ok , NW.cross ())
      c-shape comp relation caught
      (plan-untag mode′ seal★′ untag⊒ untag-shape untag-comp)
  id-widen-administration inert pending roots allocation prefix coherent
      exclusive unique wfR runtime vV noV seal★
      (C.cast-unseal hB αB∈Σ () , cʷ)
      c-shape comp relation caught (plan-unseal stored)
  id-widen-administration inert pending roots allocation prefix coherent
      exclusive unique wfR runtime vV noV seal★ c⊑ c-shape comp
      relation caught
      (plan-inst stored) =
    rightTargetWidenInstantiationRoot roots allocation prefix coherent
      exclusive unique wfR runtime vV noV cast-tag-or-id seal★-tag-or-id
      (NW.widen-mode-relax C.id-only≤tag-or-idᵈ c⊑)
      c-shape comp relation caught
  id-widen-administration inert pending roots allocation prefix coherent
      exclusive unique wfR runtime vV noV seal★ c⊑ c-shape comp
      relation caught
      plan@(plan-inst-fun-tag stored)
      with target-inst-fun-tag-plan-decompositionᵀ plan
  id-widen-administration inert pending roots allocation prefix coherent
      exclusive unique wfR runtime vV noV seal★ c⊑ c-shape comp
      relation caught
      plan@(plan-inst-fun-tag stored)
      | r ,
        inst-shape , inst-evidence , inst-comp ,
        tag-shape , tag-evidence , tag-comp ,
        inst-plan , tag-plan =
    rightTargetWidenInstFunTagRoot roots allocation prefix coherent
      exclusive unique wfR runtime vV noV cast-tag-or-id seal★-tag-or-id
      (NW.widen-mode-relax C.id-only≤tag-or-idᵈ c⊑)
      c-shape comp inst-evidence inst-comp tag-evidence tag-comp
      relation caught
  id-widen-administration inert pending roots allocation prefix coherent
      exclusive unique wfR runtime vV noV seal★
      (C.cast-seq (C.cast-untag hG gG tag-ok)
        (C.cast-gen hFun occ s⊢) , NW.cross ())
      c-shape comp relation caught (plan-fun-untag-gen stored)
  id-widen-administration inert pending roots allocation prefix coherent
      exclusive unique wfR runtime vV noV seal★
      (C.cast-seq s⊢ t⊢ , sequence-widening)
      c-shape comp relation caught
      (plan-id-widen-seq {r = r}
        seal★′ sequence⊑
        sequence-widening′ sequence-shape sequence-comp
        s-shape s-comp t-shape t-comp s-plan t-plan) =
    id-widen-sequence-resume {r = r} pending prefix seal★
      s⊢ t⊢ sequence-widening
      s-shape s-comp t-shape t-comp caught
  id-widen-administration inert pending roots allocation prefix coherent
      exclusive unique wfR runtime vV noV seal★
      (C.cast-seq s⊢ t⊢ , sequence-widening)
      c-shape comp relation caught
      (plan-widen-seq {r = r}
        mode′ seal★′ sequence⊑
        sequence-widening′ sequence-shape sequence-comp
        s-shape s-comp t-shape t-comp s-plan t-plan) =
    id-widen-sequence-resume {r = r} pending prefix seal★
      s⊢ t⊢ sequence-widening
      s-shape s-comp t-shape t-comp caught
  id-widen-administration inert pending roots allocation prefix coherent
      exclusive unique wfR runtime vV noV seal★
      (C.cast-seq s⊢ t⊢ , sequence-widening)
      c-shape comp relation caught
      (plan-narrow-seq mode′ seal★′ sequence⊒ sequence-narrowing
        sequence-shape sequence-comp
        s-shape s-comp t-shape t-comp s-plan t-plan) =
    ⊥-elim
      (narrowing-widening-sequence⊥
        sequence-narrowing sequence-widening)

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
    p [ β ↦ X ]ᴿ q →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
      ⊢ᴺ V ⊑ M′ ⦂ A ⊑ B ∶ p →
    WorldCoherentRightValueCatchupIndexedResult
      {V = V} {M′ = M′} {ρ = ρ⁺} p →
    WorldCoherentRightValueCatchupIndexedResult
      {V = V} {M′ = M′ ⟨ c ⟩} {ρ = ρ⁺} q
  reveal-administration inert roots prefix coherent exclusive unique wfR runtime
      vV noV c↑@(reveal-id-var hY ok) replacement relation caught =
    rightTargetRevealIdentityRoot roots prefix coherent exclusive unique wfR
      runtime vV noV c↑ replacement relation caught
  reveal-administration inert roots prefix coherent exclusive unique wfR runtime
      vV noV c↑@reveal-id-base replacement relation caught =
    rightTargetRevealIdentityRoot roots prefix coherent exclusive unique wfR
      runtime vV noV c↑ replacement relation caught
  reveal-administration inert roots prefix coherent exclusive unique wfR runtime
      vV noV c↑@reveal-id-★ replacement relation caught =
    rightTargetRevealIdentityRoot roots prefix coherent exclusive unique wfR
      runtime vV noV c↑ replacement relation caught
  reveal-administration inert roots prefix coherent exclusive unique wfR runtime
      vV noV c↑@(reveal-unseal hC α∈Σ ok) replacement relation caught =
    rightTargetRevealUnsealRoot roots prefix coherent exclusive unique wfR
      runtime vV noV c↑ replacement relation caught
  reveal-administration inert roots prefix coherent exclusive unique wfR runtime
      vV noV c↑@(reveal-fun {s = s} {t = t} s↓ t↑)
      replacement relation caught =
    inert prefix (s C.↦ t)
      (inj₁ (_ , _ , _ , c↑ , replacement)) caught
  reveal-administration inert roots prefix coherent exclusive unique wfR runtime
      vV noV c↑@(reveal-all {s = s} s↑) replacement relation caught =
    inert prefix (C.`∀ s)
      (inj₁ (_ , _ , _ , c↑ , replacement)) caught

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
    q [ β ↦ X ]ᴿ p →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
      ⊢ᴺ V ⊑ M′ ⦂ A ⊑ B ∶ p →
    WorldCoherentRightValueCatchupIndexedResult
      {V = V} {M′ = M′} {ρ = ρ⁺} p →
    WorldCoherentRightValueCatchupIndexedResult
      {V = V} {M′ = M′ ⟨ c ⟩} {ρ = ρ⁺} q
  conceal-administration inert roots prefix coherent
      exclusive unique wfR runtime vV noV
      c↓@(conceal-id-var hY ok) replacement relation caught =
    rightTargetConcealIdentityRoot roots prefix coherent exclusive unique wfR
      runtime vV noV c↓ replacement relation caught
  conceal-administration inert roots prefix coherent
      exclusive unique wfR runtime vV noV
      c↓@conceal-id-base replacement relation caught =
    rightTargetConcealIdentityRoot roots prefix coherent exclusive unique wfR
      runtime vV noV c↓ replacement relation caught
  conceal-administration inert roots prefix coherent
      exclusive unique wfR runtime vV noV
      c↓@conceal-id-★ replacement relation caught =
    rightTargetConcealIdentityRoot roots prefix coherent exclusive unique wfR
      runtime vV noV c↓ replacement relation caught
  conceal-administration { β = β } {X = X}
      inert roots prefix coherent exclusive unique wfR runtime vV noV
      c↓@(conceal-seal hX β∈Σ ok) replacement relation caught =
    inert prefix (C.seal X β)
      (inj₂ (inj₁ (_ , _ , _ , c↓ , replacement))) caught
  conceal-administration inert roots prefix coherent
      exclusive unique wfR runtime vV noV
      c↓@(conceal-fun {s = s} {t = t} s↑ t↓)
      replacement relation caught =
    inert prefix (s C.↦ t)
      (inj₂ (inj₁ (_ , _ , _ , c↓ , replacement))) caught
  conceal-administration inert roots prefix coherent
      exclusive unique wfR runtime vV noV
      c↓@(conceal-all {s = s} s↓) replacement relation caught =
    inert prefix (C.`∀ s)
      (inj₂ (inj₁ (_ , _ , _ , c↓ , replacement))) caught


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
          c-shape comp relation caught →
        narrow-administration inert pending roots prefix coherent
          exclusive unique wfR runtime vV noV mode seal★ c⊒ c-shape comp
          relation caught
          (targetNarrowingAdministrationPlan
            target-administration-plan-synthesisᵀ
            prefix wfR mode seal★ c⊒ c-shape comp)
    ; rightTargetWidenFrame =
        λ prefix coherent exclusive unique wfR runtime vV noV mode seal★ c⊑
          c-shape comp relation caught →
        widen-administration inert pending roots allocation prefix coherent
          exclusive unique wfR runtime vV noV mode seal★ c⊑ c-shape comp
          relation caught
          (targetWideningAdministrationPlan
            target-administration-plan-synthesisᵀ
            prefix wfR mode seal★ c⊑ c-shape comp)
    ; rightTargetIdWidenFrame =
        λ prefix coherent exclusive unique wfR runtime vV noV seal★ c⊑
          c-shape comp relation caught →
        id-widen-administration inert pending roots allocation prefix
          coherent exclusive unique wfR runtime vV noV seal★ c⊑ c-shape comp
          relation caught
          (targetIdWideningAdministrationPlan
            target-administration-plan-synthesisᵀ
            prefix wfR seal★ c⊑ c-shape comp)
    ; rightTargetRevealFrame =
        λ prefix coherent exclusive unique wfR runtime vV noV
          c↑ replacement relation caught →
        reveal-administration inert roots prefix coherent exclusive unique wfR
          runtime vV noV c↑ replacement relation caught
    ; rightTargetConcealFrame =
        λ prefix coherent exclusive unique wfR runtime vV noV
          c↓ replacement relation caught →
        conceal-administration inert roots prefix coherent exclusive unique wfR
          runtime vV noV c↓ replacement relation caught
    }

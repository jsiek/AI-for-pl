module proof.Right.Target.NuImprecisionRightTargetWidenInstPostBetaProof where

-- File Charter:
--   * Proves that the flat post-`β-inst` semantic continuation suffices for
--     the complete active target-instantiation root.
--   * Transports the full instantiation cast and its body through the
--     completed inner catch-up, takes `β-inst`, and resumes once.
--   * Contains no semantic continuation implementation, result/view/outcome
--     type, postulate, hole, permissive option, or termination bypass.

open import Data.List using (_∷_)
open import Data.Nat using (suc; zero)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import Coercions as C
import NarrowWiden as NW
open import NuReduction using
  (applyTyCtxs; keep; pure-step; β-inst; _—→[_]_)
open import NuTermImprecision using (rightStoreⁱ)
open import NuTerms using
  (No•; Value; ok-no; ok-ν; ν; _⟨_⟩)
open import QuotientedTermImprecision using
  (⊑cast⊑ᵀ)
open import Store using (StoreIncl-cons)
open import TermTyping using (SealModeStore★)
open import Types using (★; ⟰ᵗ; ⇑ᵗ)
open import proof.Right.ValueCatchup.NuImprecisionRightValueCatchupResultDef using
  ( rightCatchupIndexedResult
  ; rightCatchupSourceNoBullet
  ; rightCatchupSourceUnchanged
  ; rightCatchupSourceValue
  ; rightCatchupTargetNoBullet
  ; rightCatchupTargetValue
  )
open import proof.Catchup.Simulation.NuImprecisionSimulationCore using
  (apply-widen-inst-under-ty-binders; weak-result-target-all)
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  ( resultRightCtx
  ; resultStore
  ; canonicalIndexedResults
  ; targetCtxResult
  ; targetStoreResult
  ; targetTailChanges
  ; transportType
  ; weakIndexedResult
  )
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  (rightStoreⁱ-prefix-inclusion)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightCatchupResultDef
  using
  ( WorldCoherentRightValueCatchupIndexedResult
  ; worldRightCatchupAssumptionMembershipUnique
  ; worldRightCatchupCoherence
  ; worldRightCatchupResult
  ; worldRightCatchupSourceNameExclusive
  ; worldRightCatchupTargetStoreWf
  )
open import
  proof.Right.Target.NuImprecisionRightTargetWidenInstPostBetaDef
  using (WorldCoherentRightTargetWidenInstPostBetaᵀ)
open import
  proof.WorldCoherent.Right.Target.Resume.NuImprecisionWorldCoherentRightTargetStepResumeDef
  using (WorldCoherentRightTargetStepResumeᵀ)
open import
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetWidenInstantiationRootDef
  using (WorldCoherentRightTargetWidenInstantiationRootᵀ)
open import proof.Core.Properties.NuWideningTransport using (apply-widens-typing)
open import proof.Core.Properties.ReductionProperties using
  ( applyCoercionUnderTyBinders
  ; applyCoercions
  ; applyCoercions-inst
  )
open import proof.Core.Properties.StoreProperties using (renameStoreᵗ-incl)
open import proof.Core.Properties.TypePreservation using (seal★-inst; seal★-weaken)
open import NarrowWiden using (widen-weaken; _∣_∣_⊢_∶_⊑_)


private
  post-catchup-β-inst :
    ∀ χs {V B s} →
    Value V →
    V ⟨ applyCoercions χs (C.inst B s) ⟩
      —→[ keep ]
      ν ★ V
        (applyCoercionUnderTyBinders χs s)
  post-catchup-β-inst χs {B = B} {s = s} vV
      rewrite applyCoercions-inst χs B s =
    pure-step (β-inst vV)


world-coherent-right-target-widen-inst-from-post-beta-proofᵀ :
  WorldCoherentRightTargetStepResumeᵀ →
  WorldCoherentRightTargetWidenInstPostBetaᵀ →
  WorldCoherentRightTargetWidenInstantiationRootᵀ
world-coherent-right-target-widen-inst-from-post-beta-proofᵀ
    resume post-beta {Δᴿ = Δᴿ} {B = B} {C = C} {s = s} {q = q}
    allocation prefix coherent exclusive unique wfR runtime
    vV noV mode seal★
    (C.cast-inst hB occ s⊢ , NW.inst safe)
    relation caught
    with apply-widens-typing
      {χs = keep ∷ targetTailChanges
        (weakIndexedResult
          (rightCatchupIndexedResult
            (worldRightCatchupResult caught)))}
      mode
      (seal★-weaken
        (rightStoreⁱ-prefix-inclusion prefix) seal★)
      (widen-weaken ≤-refl
        (rightStoreⁱ-prefix-inclusion prefix)
        (C.cast-inst hB occ s⊢ , NW.inst safe))
world-coherent-right-target-widen-inst-from-post-beta-proofᵀ
    resume post-beta {Δᴿ = Δᴿ} {B = B} {C = C} {s = s} {q = q}
    allocation prefix coherent exclusive unique wfR runtime
    vV noV mode seal★
    (C.cast-inst hB occ s⊢ , NW.inst safe)
    relation caught
    | μᶠ , modeᶠ , sealᶠ , castᶠ
    with apply-widen-inst-under-ty-binders
      {χs = keep ∷ targetTailChanges
        (weakIndexedResult
          (rightCatchupIndexedResult
            (worldRightCatchupResult caught)))}
      mode
      (seal★-weaken
        (StoreIncl-cons
          (renameStoreᵗ-incl suc
            (rightStoreⁱ-prefix-inclusion prefix)))
        (seal★-inst seal★))
      (widen-weaken ≤-refl
        (StoreIncl-cons
          (renameStoreᵗ-incl suc
            (rightStoreⁱ-prefix-inclusion prefix)))
        (s⊢ , NW.instSafe→widening safe))
world-coherent-right-target-widen-inst-from-post-beta-proofᵀ
    resume post-beta {Δᴿ = Δᴿ} {B = B} {C = C} {s = s} {q = q}
    allocation prefix coherent exclusive unique wfR runtime
    vV noV mode seal★
    (C.cast-inst hB occ s⊢ , NW.inst safe)
    relation caught
    | μᶠ , modeᶠ , sealᶠ , castᶠ
    | μᵇ , modeᵇ , sealᵇ , bodyᵇ
    with weak-result-target-all
      (weakIndexedResult
        (rightCatchupIndexedResult
          (worldRightCatchupResult caught)))
world-coherent-right-target-widen-inst-from-post-beta-proofᵀ
    resume post-beta {Δᴿ = Δᴿ} {B = B} {C = C} {s = s} {q = q}
    allocation prefix coherent exclusive unique wfR runtime
    vV noV mode seal★
    (C.cast-inst hB occ s⊢ , NW.inst safe)
    relation caught
    | μᶠ , modeᶠ , sealᶠ , castᶠ
    | μᵇ , modeᵇ , sealᵇ , bodyᵇ
    | pᶠ , relationᶠ =
  resume caught framed target-step continuation
  where
  catchup = worldRightCatchupResult caught
  indexed = rightCatchupIndexedResult catchup
  inner = weakIndexedResult indexed

  final-seal :
    SealModeStore★ μᶠ (rightStoreⁱ (resultStore inner))
  final-seal =
    subst (SealModeStore★ μᶠ)
      (sym (targetStoreResult inner)) sealᶠ

  final-cast =
    subst
      (λ Δ → μᶠ ∣ Δ ∣ rightStoreⁱ (resultStore inner)
        ⊢ applyCoercions (targetTailChanges inner) (C.inst B s)
          ∶ _ ⊑ _)
      (sym (targetCtxResult inner))
      (subst
        (λ Σ → μᶠ
          ∣ applyTyCtxs (targetTailChanges inner) Δᴿ ∣ Σ
          ⊢ applyCoercions (targetTailChanges inner) (C.inst B s)
            ∶ _ ⊑ _)
        (sym (targetStoreResult inner)) castᶠ)

  framed =
    ⊑cast⊑ᵀ modeᶠ final-seal final-cast
      (canonicalIndexedResults indexed) (transportType inner q)

  target-step =
    post-catchup-β-inst
      (targetTailChanges inner) (rightCatchupTargetValue catchup)

  final-body-seal =
    subst
      (λ Σ → SealModeStore★ (C.instᵈ μᵇ)
        ((zero , ★) ∷ ⟰ᵗ Σ))
      (sym (targetStoreResult inner)) sealᵇ

  final-body =
    subst
      (λ Δ → C.instᵈ μᵇ ∣ suc Δ
        ∣ (zero , ★) ∷
            ⟰ᵗ (rightStoreⁱ (resultStore inner))
        ⊢ applyCoercionUnderTyBinders (targetTailChanges inner) s
          ∶ _ ⊑ ⇑ᵗ _)
      (sym (targetCtxResult inner))
      (subst
        (λ Σ → C.instᵈ μᵇ
          ∣ suc
              (applyTyCtxs (targetTailChanges inner) Δᴿ)
          ∣ (zero , ★) ∷ ⟰ᵗ Σ
          ⊢ applyCoercionUnderTyBinders (targetTailChanges inner) s
            ∶ _ ⊑ ⇑ᵗ _)
        (sym (targetStoreResult inner)) bodyᵇ)

  continuation =
    post-beta
      (worldRightCatchupCoherence caught)
      (worldRightCatchupSourceNameExclusive caught)
      (worldRightCatchupAssumptionMembershipUnique caught)
      (worldRightCatchupTargetStoreWf caught)
      (ok-ν (ok-no (rightCatchupTargetNoBullet catchup)))
      final-source-value
      final-source-no-bullet
      (rightCatchupTargetValue catchup)
      (rightCatchupTargetNoBullet catchup)
      modeᵇ final-body-seal final-body relationᶠ
    where
    final-source-value =
      subst Value
        (sym (rightCatchupSourceUnchanged catchup))
        (rightCatchupSourceValue catchup)

    final-source-no-bullet =
      subst No•
        (sym (rightCatchupSourceUnchanged catchup))
        (rightCatchupSourceNoBullet catchup)

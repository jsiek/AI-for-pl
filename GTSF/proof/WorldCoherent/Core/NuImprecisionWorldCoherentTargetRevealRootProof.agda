module proof.WorldCoherent.Core.NuImprecisionWorldCoherentTargetRevealRootProof where

-- File Charter:
--   * Proves the world-coherent target reveal-unseal root contract.
--   * Catches the source up to a value or blame, then cancels the target seal.
--   * Retargets the catch-up result while preserving all transport evidence.

open import Agda.Builtin.Equality using (_≡_; refl)
import Coercions as C
open import Data.List using ([])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuReduction using (applyTy; applyTys; keep; ↠-refl)
open import NuStore using (StoreWf)
open import NuTermImprecision using
  (StoreImp; rightStoreⁱ)
open import NuTerms using
  (No•; RuntimeOK; Term; Value; blame; _⟨_⟩)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using (Ty; TyVar; ＇_)
open import proof.DGG.Core.NuProgress using (runtime-value-no•)
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  ( LeftCatchupIndexedResult
  ; WeakOneStepIndexedResult
  ; WeakOneStepResult
  ; WeakOneStepTransport
  ; WeakOneStepTypeCoherence
  ; canonicalIndexedResults
  ; catchupIndexedInvariant
  ; catchupIndexedResult
  ; resultCtx
  ; resultLeftCtx
  ; resultRightCtx
  ; resultStore
  ; silentInvariant
  ; sourceCatchup
  ; sourceChanges
  ; sourceCtxResult
  ; sourceIsValueOrBlame
  ; sourceResult
  ; sourceStoreResult
  ; targetCtxResult
  ; targetIsUnchanged
  ; targetResult
  ; targetStoreResult
  ; targetTailChanges
  ; targetTailIsEmpty
  ; transportAllBody
  ; transportNo•Terms
  ; transportRightBody
  ; transportSourceNu
  ; transportType
  ; transportArrowCoherent
  ; transportAllCoherent
  ; weak-indexed-result
  ; weak-step-result
  ; weak-step-transport
  ; weak-step-type-coherence
  ; weakIndexedResult
  ; weakIndexedTransport
  ; weakIndexedTypeCoherence
  )
open import proof.Target.SealTag.NuImprecisionTargetSealCancellationDef using
  (TargetSealCancellationᵀ)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef using
  ( WorldCoherentWeakOneStepIndexedOutcome
  ; WorldCoherentLeftCatchupIndexedResult
  ; world-coherent-left-indexed-catchup
  ; world-indexed-outcome-related
  ; world-indexed-outcome-source-blame
  )
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherentTargetRevealRootDef using
  (WorldCoherentTargetRevealRootᵀ)
open import proof.WorldCoherent.Value.NuImprecisionWorldCoherentValueCatchupDef using
  (WorldCoherentLeftValueCatchupᵀ)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)


target-reveal-retarget-resultᵀ :
  ∀ {Φ Δᴸ Δᴿ} {M V : Term} {A X X′ : Ty} {β : TyVar}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ ＇ β ⊣ Δᴿ}
    (q : Φ ∣ Δᴸ ⊢ A ⊑ X′ ⊣ Δᴿ)
    (catchup : LeftCatchupIndexedResult
      {N = M} {V′ = V ⟨ C.seal X β ⟩} {ρ = ρ} p) →
  targetTailChanges
      (weakIndexedResult (catchupIndexedResult catchup)) ≡ [] →
  targetResult (weakIndexedResult (catchupIndexedResult catchup))
    ≡ V ⟨ C.seal X β ⟩ →
  (let old = weakIndexedResult (catchupIndexedResult catchup) in
   resultCtx old ∣ resultLeftCtx old ∣ resultRightCtx old
     ∣ resultStore old ∣ []
     ⊢ᴺ sourceResult old ⊑ V
       ⦂ applyTys (sourceChanges old) A
       ⊑ applyTys (targetTailChanges old) (applyTy keep X′)
       ∶ transportType old q) →
  WeakOneStepIndexedResult
    {M = M} {N′ = V} {χ = keep} {ρ = ρ} q
target-reveal-retarget-resultᵀ
    {M = M} {V = V} {A = A} {X′ = X′} {ρ = ρ}
    q catchup refl refl related =
  weak-indexed-result result related transport coherence
  where
  old = weakIndexedResult (catchupIndexedResult catchup)
  transport =
    weak-step-transport
      (transportNo•Terms
        (weakIndexedTransport (catchupIndexedResult catchup)))
  coherence =
    weak-step-type-coherence
      (transportArrowCoherent
        (weakIndexedTypeCoherence (catchupIndexedResult catchup)))
      (transportAllCoherent
        (weakIndexedTypeCoherence (catchupIndexedResult catchup)))

  result : WeakOneStepResult ρ M V A X′ keep
  result =
    weak-step-result
      (sourceChanges old)
      []
      (sourceResult old)
      V
      (resultCtx old)
      (resultLeftCtx old)
      (resultRightCtx old)
      (sourceCtxResult old)
      (targetCtxResult old)
      (resultStore old)
      (applyTys (sourceChanges old) A)
      X′
      refl
      refl
      (transportType old)
      (transportAllBody old)
      (transportRightBody old)
      (transportSourceNu old)
      (transportType old q)
      (sourceCatchup old)
      ↠-refl
      (sourceStoreResult old)
      (targetStoreResult old)
      related


target-reveal-retarget-transportᵀ :
  ∀ {Φ Δᴸ Δᴿ} {M V : Term} {A X X′ : Ty} {β : TyVar}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ ＇ β ⊣ Δᴿ}
    (q : Φ ∣ Δᴸ ⊢ A ⊑ X′ ⊣ Δᴿ)
    (catchup : LeftCatchupIndexedResult
      {N = M} {V′ = V ⟨ C.seal X β ⟩} {ρ = ρ} p)
    (tail-empty : targetTailChanges
      (weakIndexedResult (catchupIndexedResult catchup)) ≡ [])
    (target-same :
      targetResult (weakIndexedResult (catchupIndexedResult catchup))
        ≡ V ⟨ C.seal X β ⟩)
    (related :
      let old = weakIndexedResult (catchupIndexedResult catchup) in
      resultCtx old ∣ resultLeftCtx old ∣ resultRightCtx old
        ∣ resultStore old ∣ []
        ⊢ᴺ sourceResult old ⊑ V
          ⦂ applyTys (sourceChanges old) A
          ⊑ applyTys (targetTailChanges old) (applyTy keep X′)
          ∶ transportType old q) →
  WeakOneStepTransport
    (weakIndexedResult
      (target-reveal-retarget-resultᵀ
        q catchup tail-empty target-same related))
target-reveal-retarget-transportᵀ q catchup refl refl related =
  weakIndexedTransport
    (target-reveal-retarget-resultᵀ q catchup refl refl related)


target-reveal-retarget-coherenceᵀ :
  ∀ {Φ Δᴸ Δᴿ} {M V : Term} {A X X′ : Ty} {β : TyVar}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ ＇ β ⊣ Δᴿ}
    (q : Φ ∣ Δᴸ ⊢ A ⊑ X′ ⊣ Δᴿ)
    (catchup : LeftCatchupIndexedResult
      {N = M} {V′ = V ⟨ C.seal X β ⟩} {ρ = ρ} p)
    (tail-empty : targetTailChanges
      (weakIndexedResult (catchupIndexedResult catchup)) ≡ [])
    (target-same :
      targetResult (weakIndexedResult (catchupIndexedResult catchup))
        ≡ V ⟨ C.seal X β ⟩)
    (related :
      let old = weakIndexedResult (catchupIndexedResult catchup) in
      resultCtx old ∣ resultLeftCtx old ∣ resultRightCtx old
        ∣ resultStore old ∣ []
        ⊢ᴺ sourceResult old ⊑ V
          ⦂ applyTys (sourceChanges old) A
          ⊑ applyTys (targetTailChanges old) (applyTy keep X′)
          ∶ transportType old q) →
  WeakOneStepTypeCoherence
    (weakIndexedResult
      (target-reveal-retarget-resultᵀ
        q catchup tail-empty target-same related))
target-reveal-retarget-coherenceᵀ q catchup refl refl related =
  weakIndexedTypeCoherence
    (target-reveal-retarget-resultᵀ q catchup refl refl related)


world-coherent-target-reveal-root-proofᵀ :
  WorldCoherentLeftValueCatchupᵀ →
  TargetSealCancellationᵀ →
  WorldCoherentTargetRevealRootᵀ
world-coherent-target-reveal-root-proofᵀ
    catchup cancel {X = X} {X′ = X′} {β = β} {ρ = ρ}
    coherent exclusive wfL wfΣ okM okVβ vV βX′∈Σ M⊑Vβ q
    with catchup coherent exclusive wfL okM (vV ⟨ C.seal X β ⟩)
      (runtime-value-no• okVβ (vV ⟨ C.seal X β ⟩)) M⊑Vβ
world-coherent-target-reveal-root-proofᵀ
    catchup cancel
    coherent exclusive wfL wfΣ okM okVβ vV βX′∈Σ M⊑Vβ q
    | world-coherent-left-indexed-catchup
        caught caught-lineage final-coherent final-exclusive final-wfL
    with sourceIsValueOrBlame (catchupIndexedInvariant caught)
world-coherent-target-reveal-root-proofᵀ
    catchup cancel
    coherent exclusive wfL wfΣ okM okVβ vV βX′∈Σ M⊑Vβ q
    | world-coherent-left-indexed-catchup
        caught caught-lineage final-coherent final-exclusive final-wfL
    | inj₂ refl =
  world-indexed-outcome-source-blame
    (sourceCatchup (weakIndexedResult (catchupIndexedResult caught)))
world-coherent-target-reveal-root-proofᵀ
    catchup cancel
    coherent exclusive wfL wfΣ okM okVβ vV βX′∈Σ M⊑Vβ q
    | world-coherent-left-indexed-catchup
        caught caught-lineage final-coherent final-exclusive final-wfL
    | inj₁ (vW , noW)
    with targetTailIsEmpty
           (silentInvariant (catchupIndexedInvariant caught))
       | targetIsUnchanged
           (silentInvariant (catchupIndexedInvariant caught))
world-coherent-target-reveal-root-proofᵀ
    catchup cancel {X′ = X′} {β = β} {ρ = ρ}
    coherent exclusive wfL wfΣ okM okVβ vV βX′∈Σ M⊑Vβ q
    | world-coherent-left-indexed-catchup
        caught caught-lineage final-coherent final-exclusive final-wfL
    | inj₁ (vW , noW) | refl | refl =
  world-indexed-outcome-related
    retargeted
    final-coherent
    final-exclusive
  where
  old = weakIndexedResult (catchupIndexedResult caught)

  final-wf =
    subst (StoreWf (resultRightCtx old))
      (sym (targetStoreResult old))
      (subst (λ Δ → StoreWf Δ (rightStoreⁱ ρ))
        (sym (targetCtxResult old)) wfΣ)

  final-βX′∈Σ =
    subst (λ Σ → (β , X′) ∈ Σ)
      (sym (targetStoreResult old)) βX′∈Σ

  canceled =
    cancel final-coherent final-wf vW noW vV final-βX′∈Σ
      (canonicalIndexedResults (catchupIndexedResult caught))
      (transportType old q)

  retargeted =
    target-reveal-retarget-resultᵀ q caught refl refl canceled

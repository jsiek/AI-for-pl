module proof.NuDGGTerminalBackwardValueWorldCoherentProof where

-- File Charter:
--   * Proves the world-coherent backward-value terminal contract from its
--     world-coherent one-step and value catch-up dependency contracts.
--   * Threads world coherence and source-name exclusivity through the fuel
--     induction and unwraps them only at the terminal boundary.
--   * Reuses the generic trace composition helpers without importing either
--     live partial simulation implementation.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_; _++_; length)
open import Data.Nat using (ℕ; zero; suc; s≤s⁻¹; _≤_)
open import Data.Nat.Properties using (≤-refl; ≤-trans)
open import Data.Product using (_×_; _,_; Σ-syntax; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuReduction using
  ( StoreChanges
  ; applyStores
  ; applyTyCtxs
  ; applyTys
  ; ↠-refl
  ; ↠-step
  ; _—↠[_]_
  )
open import NuStore using (StoreWf)
open import NuTermImprecision using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using (RuntimeOK; Term; Value; blame)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import proof.NuDGGTerminalBackwardValueProof using
  ( empty-context-source-typing
  ; empty-context-target-typing
  ; prepend-weak-related-valueᵀ
  )
open import proof.NuDGGTerminalBackwardValueWorldCoherentDef using
  (WorldCoherentBackwardTargetValueOrSourceBlameᵀ)
open import proof.NuDGGTraceAlignment using
  (weak-result-target-prefix-valueᵀ)
open import proof.NuDGGTraceMeasure using
  (aligned-residual-shorter)
open import proof.NuDGGWeakResultPreservation using
  ( weak-result-source-store-wf
  ; weak-result-source-runtime
  ; weak-result-target-store-wf
  ; weak-result-target-runtime
  )
open import proof.ReductionProperties using (↠-trans)
open import proof.NuProgress using (runtime-value-no•)
open import proof.NuImprecisionSimulationResultDef using
  ( canonicalIndexedResults
  ; catchupIndexedInvariant
  ; catchupIndexedResult
  ; resultCtx
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
  ; targetTailChanges
  ; targetTailIsEmpty
  ; targetStoreResult
  ; transportType
  ; weakIndexedResult
  )
open import proof.NuImprecisionWorldCoherentOneStepDef using
  (WorldCoherentWeakOneStepIndexedSimulationᵀ)
open import proof.NuImprecisionWorldCoherentResultDef using
  ( WorldCoherentLeftCatchupIndexedResult
  ; WorldCoherentWeakOneStepIndexedOutcome
  ; world-coherent-left-indexed-catchup
  ; world-indexed-outcome-related
  ; world-indexed-outcome-source-blame
  )
open import proof.NuImprecisionWorldCoherentValueCatchupDef using
  (WorldCoherentLeftValueCatchupᵀ)
open import proof.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)


world-coherent-backward-target-value-or-source-blame-proofᵀ :
  WorldCoherentWeakOneStepIndexedSimulationᵀ →
  WorldCoherentLeftValueCatchupᵀ →
  WorldCoherentBackwardTargetValueOrSourceBlameᵀ
world-coherent-backward-target-value-or-source-blame-proofᵀ
    one-step target-value-catchup
    coherent exclusive wfL wfR okM okM′ M⊑M′
    V′ χs′ M′↠V′ vV′ =
  go (length χs′) coherent exclusive wfL wfR okM okM′ M⊑M′
    V′ χs′ M′↠V′ vV′ ≤-refl
  where
  go :
    ∀ (fuel : ℕ) {Φ Δᴸ Δᴿ M M′ A B}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    WorldCoherent ρ →
    SourceNameExclusive Φ →
    StoreWf Δᴸ (leftStoreⁱ ρ) →
    StoreWf Δᴿ (rightStoreⁱ ρ) →
    RuntimeOK M →
    RuntimeOK M′ →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
    ∀ (V′ : Term) (ψs : StoreChanges) →
    M′ —↠[ ψs ] V′ →
    Value V′ →
    length ψs ≤ fuel →
      (∃[ V ] (Σ[ χs ∈ StoreChanges ]
      (∃[ Ψ ] (Σ[ ρ′ ∈
          StoreImp Ψ
            (applyTyCtxs χs Δᴸ) (applyTyCtxs ψs Δᴿ) ]
      (Σ[ q ∈
          (Ψ ∣ applyTyCtxs χs Δᴸ
            ⊢ applyTys χs A ⊑ applyTys ψs B
            ⊣ applyTyCtxs ψs Δᴿ) ]
        ((M —↠[ χs ] V) ×
         Value V ×
         (leftStoreⁱ ρ′ ≡ applyStores χs (leftStoreⁱ ρ)) ×
         (rightStoreⁱ ρ′ ≡ applyStores ψs (rightStoreⁱ ρ)) ×
         Ψ ∣ applyTyCtxs χs Δᴸ ∣ applyTyCtxs ψs Δᴿ ∣ ρ′ ∣ []
           ⊢ᴺ V ⊑ V′
           ⦂ applyTys χs A ⊑ applyTys ψs B ∶ q)))))
      ⊎ (∃[ χs ] (M —↠[ χs ] blame)))
  go zero coherent exclusive wfL wfR okM okM′ M⊑M′ V′ []
      ↠-refl vV′ bound
    with target-value-catchup coherent exclusive wfL okM vV′
      (runtime-value-no• okM′ vV′) M⊑M′
  go zero coherent exclusive wfL wfR okM okM′ M⊑M′ V′ []
      ↠-refl vV′ bound
    | world-coherent-left-indexed-catchup
        catchup catchup-lineage final-coherent final-exclusive final-wfL
    with sourceIsValueOrBlame
      (catchupIndexedInvariant catchup)
  go zero {p = p} coherent exclusive wfL wfR okM okM′ M⊑M′ V′ []
      ↠-refl vV′ bound
    | world-coherent-left-indexed-catchup
        catchup catchup-lineage final-coherent final-exclusive final-wfL
    | inj₁ (vV , noV)
    with sourceCtxResult
           (weakIndexedResult (catchupIndexedResult catchup))
       | targetCtxResult
           (weakIndexedResult (catchupIndexedResult catchup))
       | targetTailIsEmpty
           (silentInvariant (catchupIndexedInvariant catchup))
       | targetIsUnchanged
           (silentInvariant (catchupIndexedInvariant catchup))
  go zero {p = p} coherent exclusive wfL wfR okM okM′ M⊑M′ V′ []
      ↠-refl vV′ bound
    | world-coherent-left-indexed-catchup
        catchup catchup-lineage final-coherent final-exclusive final-wfL
    | inj₁ (vV , noV) | refl | refl | refl | refl =
      inj₁
        ( sourceResult (weakIndexedResult (catchupIndexedResult catchup))
        , sourceChanges (weakIndexedResult (catchupIndexedResult catchup))
        , resultCtx (weakIndexedResult (catchupIndexedResult catchup))
        , resultStore (weakIndexedResult (catchupIndexedResult catchup))
        , transportType
            (weakIndexedResult (catchupIndexedResult catchup)) p
        , sourceCatchup
            (weakIndexedResult (catchupIndexedResult catchup))
        , vV
        , sourceStoreResult
            (weakIndexedResult (catchupIndexedResult catchup))
        , targetStoreResult
            (weakIndexedResult (catchupIndexedResult catchup))
        , canonicalIndexedResults (catchupIndexedResult catchup)
        )
  go zero coherent exclusive wfL wfR okM okM′ M⊑M′ V′ []
      ↠-refl vV′ bound
    | world-coherent-left-indexed-catchup
        catchup catchup-lineage final-coherent final-exclusive final-wfL
    | inj₂ refl =
      inj₂
        ( sourceChanges (weakIndexedResult (catchupIndexedResult catchup))
        , sourceCatchup
            (weakIndexedResult (catchupIndexedResult catchup))
        )
  go zero coherent exclusive wfL wfR okM okM′ M⊑M′ V′
      (χ ∷ ψs) (↠-step target-step target-rest) vV′ ()
  go (suc fuel) coherent exclusive wfL wfR okM okM′ M⊑M′ V′ []
      ↠-refl vV′ bound =
    go zero coherent exclusive wfL wfR okM okM′ M⊑M′ V′ []
      ↠-refl vV′ ≤-refl
  go (suc fuel) coherent exclusive wfL wfR okM okM′ M⊑M′ V′
      (χ ∷ ψs) (↠-step target-step target-rest) vV′ bound
    with one-step
      coherent exclusive wfL wfR okM okM′ M⊑M′ target-step
  go (suc fuel) coherent exclusive wfL wfR okM okM′ M⊑M′ V′
      (χ ∷ ψs) (↠-step target-step target-rest) vV′ bound
    | world-indexed-outcome-source-blame
        {χs = source-blame-changes} source-blame =
      inj₂ (source-blame-changes , source-blame)
  go (suc fuel) coherent exclusive wfL wfR okM okM′ M⊑M′ V′
      (χ ∷ ψs) (↠-step target-step target-rest) vV′ bound
    | world-indexed-outcome-related
        indexed successor-coherent successor-exclusive
    with weak-result-target-prefix-valueᵀ
      (weakIndexedResult indexed) target-rest vV′
  go (suc fuel) coherent exclusive wfL wfR okM okM′ M⊑M′ V′
      (χ ∷ ψs) (↠-step target-step target-rest) vV′ bound
    | world-indexed-outcome-related
        indexed successor-coherent successor-exclusive
    | residual-changes , target-result↠V′ , trace-eq
    with go fuel successor-coherent successor-exclusive
      (weak-result-source-store-wf
        (weakIndexedResult indexed) wfL okM
        (empty-context-source-typing M⊑M′))
      (weak-result-target-store-wf
        (weakIndexedResult indexed) wfR okM′
        (empty-context-target-typing M⊑M′) target-step)
      (weak-result-source-runtime
        (weakIndexedResult indexed) wfL okM
        (empty-context-source-typing M⊑M′))
      (weak-result-target-runtime
        (weakIndexedResult indexed) wfR okM′
        (empty-context-target-typing M⊑M′) target-step)
      (canonicalIndexedResults indexed)
      V′ residual-changes target-result↠V′ vV′
      (s≤s⁻¹
        (≤-trans
          (aligned-residual-shorter
            {χ = χ}
            {observed = ψs}
            {administrative =
              targetTailChanges (weakIndexedResult indexed)}
            {residual = residual-changes}
            trace-eq)
          bound))
  go (suc fuel) coherent exclusive wfL wfR okM okM′ M⊑M′ V′
      (χ ∷ ψs) (↠-step target-step target-rest) vV′ bound
    | world-indexed-outcome-related
        indexed successor-coherent successor-exclusive
    | residual-changes , target-result↠V′ , trace-eq
    | inj₂ (result-blame-changes , source-result↠blame) =
      inj₂
        ( sourceChanges (weakIndexedResult indexed) ++
            result-blame-changes
        , ↠-trans (sourceCatchup (weakIndexedResult indexed))
                  source-result↠blame
        )
  go (suc fuel) coherent exclusive wfL wfR okM okM′ M⊑M′ V′
      (χ ∷ ψs) (↠-step target-step target-rest) vV′ bound
    | world-indexed-outcome-related
        indexed successor-coherent successor-exclusive
    | residual-changes , target-result↠V′ , trace-eq
    | inj₁ (V , result-source-changes , Ψ , ρ′ , q ,
        source-result↠V , vV , left-store-eq , right-store-eq , V⊑V′) =
      inj₁
        ( V
        , sourceChanges (weakIndexedResult indexed) ++
            result-source-changes
        , Ψ
        , prepend-weak-related-valueᵀ
            indexed trace-eq ρ′ q source-result↠V vV
            left-store-eq right-store-eq V⊑V′
        )

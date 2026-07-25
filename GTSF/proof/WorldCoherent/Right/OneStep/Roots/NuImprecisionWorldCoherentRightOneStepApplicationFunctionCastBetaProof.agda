module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationFunctionCastBetaProof
  where

-- File Charter:
--   * Catches an arbitrary source function before target function-cast beta.
--   * Frames the silent function catch-up around the untouched argument, then
--     invokes the exact-rank source-function-value scheduler.
--   * Preserves transport, type coherence, relational-store lineage, and every
--     final-world invariant.
--   * Contains no semantic recursion, postulate, hole, permissive option,
--     catch-all, or compatibility wrapper.

import Coercions as C
open import Agda.Builtin.Equality using (refl)
open import Data.List using ([])
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Sum using
  ( inj₁
  ; inj₂
  )
open import ImprecisionWf using
  ( ImpCtx
  ; _↦_
  ; _∣_⊢_⊑_⊣_
  )
open import NuReduction using (keep)
open import NuStore using (StoreWf)
open import NuTermImprecision using
  ( StoreImp
  ; leftStoreⁱ
  )
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; Term
  ; Value
  ; no•-·
  ; ok-no
  ; ok-·₁
  ; ok-·₂
  ; _·_
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using
  ( Ty
  ; TyCtx
  ; _⇒_
  )
open import
  proof.Catchup.Simulation.NuImprecisionSimulationCore
  using
  ( ·₁-blame-tail
  ; weak-indexed-arrow-resultᵀ
  ; weak-one-step-·₁-frame-preserves-transportᵀ
  ; weak-one-step-·₁-frame-preserves-type-coherenceᵀ
  ; weak-one-step-·₁-frameᵀ
  )
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  ( LeftSilentIndexedResult
  ; canonicalArrowResults
  ; catchupIndexedInvariant
  ; catchupIndexedResult
  ; left-silent-indexed
  ; left-silent-invariant
  ; relatedResults
  ; silentInvariant
  ; sourceCatchup
  ; sourceChanges
  ; sourceIsValueOrBlame
  ; targetIsUnchanged
  ; targetTailIsEmpty
  ; transportNo•Terms
  ; weak-indexed-result
  ; weakIndexedResult
  ; weakIndexedTransport
  ; weakIndexedTypeCoherence
  ; weakArrowResult
  )
open import
  proof.Core.Properties.ReductionProperties
  using (applyTerms-preserves-No•)
open import
  proof.DGG.Core.NuPreservation
  using
  ( runtime-·₁
  ; runtime-·₂
  ; value-runtime-No•
  )
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using (AssumptionMembershipUnique)
open import
  proof.NuCore.Relations.NuImprecisionContextExclusivityDef
  using (SourceNameExclusive)
open import
  proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef
  using
  ( lineageEmbedding
  ; lineagePrefix
  ; lineageStore
  ; weak-step-store-lineage
  )
open import
  proof.Target.FunctionCast.NuImprecisionTargetFunctionCastSpineMeasureDef
  using (targetFunctionCastSpineRank)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef
  using (WorldCoherent)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentLeftSilentOutcomeComposition
  using (world-coherent-left-silent-then-outcomeᵀ)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using
  ( WorldCoherentWeakOneStepIndexedOutcome
  ; world-coherent-left-indexed-catchup
  ; world-indexed-outcome-source-blame
  )
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationFunctionCastBetaDef
  using (WorldCoherentRightOneStepApplicationFunctionCastBetaᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationFunctionCastBetaRankedDef
  using
  (WorldCoherentRightOneStepApplicationFunctionCastBetaSourceFunctionValueAtᵀ)
open import
  proof.WorldCoherent.Value.NuImprecisionWorldCoherentValueCatchupDef
  using (WorldCoherentLeftValueCatchupᵀ)


private
  catch-source-function-then-finishᵀ :
    WorldCoherentLeftValueCatchupᵀ →
    (∀ n →
      WorldCoherentRightOneStepApplicationFunctionCastBetaSourceFunctionValueAtᵀ
        n) →
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {L M V′ W′ : Term} {e f : C.Coercion}
      {A A′ B B′ : Ty}
      {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
    WorldCoherent ρ →
    SourceNameExclusive Φ →
    AssumptionMembershipUnique Φ →
    StoreWf Δᴸ (leftStoreⁱ ρ) →
    RuntimeOK L →
    No• M →
    RuntimeOK ((V′ ⟨ e C.↦ f ⟩) · W′) →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ L ⊑ V′ ⟨ e C.↦ f ⟩
        ⦂ A ⇒ B ⊑ A′ ⇒ B′ ∶ pA ↦ pB →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ M ⊑ W′ ⦂ A ⊑ A′ ∶ pA →
    Value V′ →
    Value W′ →
    WorldCoherentWeakOneStepIndexedOutcome
      {M = L · M}
      {N′ = (V′ · (W′ ⟨ e ⟩)) ⟨ f ⟩}
      {χ = keep} {ρ = ρ} pB
  catch-source-function-then-finishᵀ
      catchup terminal
      {V′ = V′} {W′ = W′} {e = e} {f = f}
      coherent exclusive unique wfL okL noM okM′
      function-related argument-related vV′ vW′
      with catchup coherent exclusive unique wfL
        okL target-function-value target-function-no function-related
    where
    target-function-value = vV′ ⟨ e C.↦ f ⟩
    target-function-no =
      value-runtime-No• target-function-value (runtime-·₁ okM′)
  catch-source-function-then-finishᵀ
      catchup terminal
      {V′ = V′} {W′ = W′} {e = e} {f = f}
      coherent exclusive unique wfL okL noM okM′
      function-related argument-related vV′ vW′
      | world-coherent-left-indexed-catchup
          caught caught-lineage final-coherent final-exclusive final-unique
          final-wfL
      with sourceIsValueOrBlame (catchupIndexedInvariant caught)
  catch-source-function-then-finishᵀ
      catchup terminal
      {V′ = V′} {W′ = W′} {e = e} {f = f}
      coherent exclusive unique wfL okL noM okM′
      function-related argument-related vV′ vW′
      | world-coherent-left-indexed-catchup
          caught caught-lineage final-coherent final-exclusive final-unique
          final-wfL
      | inj₂ refl =
    world-indexed-outcome-source-blame
      (·₁-blame-tail noM
        (sourceCatchup
          (weakIndexedResult (catchupIndexedResult caught))))
  catch-source-function-then-finishᵀ
      catchup terminal
      {V′ = V′} {W′ = W′} {e = e} {f = f}
      coherent exclusive unique wfL okL noM okM′
      function-related argument-related vV′ vW′
      | world-coherent-left-indexed-catchup
          caught caught-lineage final-coherent final-exclusive final-unique
          final-wfL
      | inj₁ (vK , noK)
      with targetTailIsEmpty
             (silentInvariant (catchupIndexedInvariant caught))
         | targetIsUnchanged
             (silentInvariant (catchupIndexedInvariant caught))
  catch-source-function-then-finishᵀ
      catchup terminal
      {V′ = V′} {W′ = W′} {e = e} {f = f}
      coherent exclusive unique wfL okL noM okM′
      function-related argument-related vV′ vW′
      | world-coherent-left-indexed-catchup
          caught caught-lineage final-coherent final-exclusive final-unique
          final-wfL
      | inj₁ (vK , noK) | refl | refl =
    world-coherent-left-silent-then-outcomeᵀ
      framed-silent framed-lineage final-outcome
    where
    caught-indexed = catchupIndexedResult caught
    caught-arrow = weak-indexed-arrow-resultᵀ caught-indexed
    caught-raw = weakArrowResult caught-arrow
    function-final = canonicalArrowResults caught-arrow

    target-function-value = vV′ ⟨ e C.↦ f ⟩
    target-function-no =
      value-runtime-No• target-function-value (runtime-·₁ okM′)
    target-argument-no =
      value-runtime-No• vW′
        (runtime-·₂ target-function-value okM′)
    transported-argument =
      transportNo•Terms
        (weakIndexedTransport caught-indexed)
        noM target-argument-no argument-related

    framed-raw =
      weak-one-step-·₁-frameᵀ
        noM target-argument-no caught-raw
        function-final transported-argument
    framed-indexed =
      weak-indexed-result framed-raw (relatedResults framed-raw)
        (weak-one-step-·₁-frame-preserves-transportᵀ
          noM target-argument-no caught-raw
          function-final transported-argument
          (weakIndexedTransport caught-indexed))
        (weak-one-step-·₁-frame-preserves-type-coherenceᵀ
          noM target-argument-no caught-raw
          function-final transported-argument
          (weakIndexedTypeCoherence caught-indexed))

    transported-argument-no =
      applyTerms-preserves-No•
        (sourceChanges caught-raw) noM

    framed-silent : LeftSilentIndexedResult _
    framed-silent =
      left-silent-indexed framed-indexed
        (left-silent-invariant refl refl)
        (ok-no (no•-· noK transported-argument-no))

    framed-lineage =
      weak-step-store-lineage
        (lineageStore caught-lineage)
        (lineageEmbedding caught-lineage)
        (lineagePrefix caught-lineage)

    final-outcome =
      terminal (targetFunctionCastSpineRank vK)
        final-coherent final-exclusive final-unique final-wfL
        (ok-no (no•-· noK transported-argument-no))
        okM′
        function-final transported-argument
        vK vV′ vW′ refl


world-coherent-right-one-step-application-function-cast-beta-proofᵀ :
  WorldCoherentLeftValueCatchupᵀ →
  (∀ n →
    WorldCoherentRightOneStepApplicationFunctionCastBetaSourceFunctionValueAtᵀ
      n) →
  WorldCoherentRightOneStepApplicationFunctionCastBetaᵀ
world-coherent-right-one-step-application-function-cast-beta-proofᵀ
    catchup terminal
    coherent exclusive unique wfL
    (ok-no (no•-· noL noM)) okM′
    function-related argument-related vV′ vW′ =
  catch-source-function-then-finishᵀ
    catchup terminal coherent exclusive unique wfL
    (ok-no noL) noM okM′
    function-related argument-related vV′ vW′
world-coherent-right-one-step-application-function-cast-beta-proofᵀ
    catchup terminal
    coherent exclusive unique wfL
    (ok-·₁ okL noM) okM′
    function-related argument-related vV′ vW′ =
  catch-source-function-then-finishᵀ
    catchup terminal coherent exclusive unique wfL
    okL noM okM′
    function-related argument-related vV′ vW′
world-coherent-right-one-step-application-function-cast-beta-proofᵀ
    catchup terminal
    coherent exclusive unique wfL
    okApp@(ok-·₂ vL noL okArg) okM′
    function-related argument-related vV′ vW′ =
  terminal (targetFunctionCastSpineRank vL)
    coherent exclusive unique wfL okApp okM′
    function-related argument-related vL vV′ vW′ refl

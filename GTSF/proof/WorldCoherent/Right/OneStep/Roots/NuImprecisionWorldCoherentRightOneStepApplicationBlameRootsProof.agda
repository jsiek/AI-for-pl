module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationBlameRootsProof
  where

-- File Charter:
--   * Implements both target application-blame roots for world-coherent
--     target-oriented one-step simulation.
--   * Exhaustively separates source applications whose function must catch
--     up from those whose function is already a value.
--   * Every branch constructs a source reduction sequence to blame.
--   * Contains no recursive dispatcher, postulate, hole, permissive option,
--     continuing related branch, or compatibility wrapper.

open import Agda.Builtin.Equality using (refl)
open import Data.Empty using (⊥-elim)
open import Data.List using ([])
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import ImprecisionWf using
  ( ImpCtx
  ; _↦_
  ; _∣_⊢_⊑_⊣_
  )
open import NuReduction using
  ( keep
  ; applyTerms
  )
open import NuStore using (StoreWf)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; leftStoreⁱ
  )
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; Term
  ; Value
  ; blame
  ; no•-blame
  ; no•-·
  ; ok-no
  ; ok-·₁
  ; ok-·₂
  ; _·_
  )
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using
  ( Ty
  ; TyCtx
  ; _⇒_
  )
open import proof.Catchup.Simulation.NuImprecisionSimulationCore using
  ( ·₁-blame-tail
  ; ·₂-blame-tail
  )
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  ( catchupIndexedInvariant
  ; catchupIndexedResult
  ; silentInvariant
  ; sourceCatchup
  ; sourceChanges
  ; sourceIsValueOrBlame
  ; targetTailIsEmpty
  ; transportNo•Terms
  ; weakIndexedResult
  ; weakIndexedTransport
  )
open import proof.Core.Properties.ReductionProperties using
  ( ·₁-↠
  ; applyTerms-preserves-No•
  ; ↠-trans
  )
open import proof.Target.Core.NuImprecisionTargetBlameCatchup using
  ( left-catchup-target-blameᵀ
  ; value-not-target-blameᵀ
  )
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using (AssumptionMembershipUnique)
open import
  proof.NuCore.Relations.NuImprecisionContextExclusivityDef
  using (SourceNameExclusive)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef
  using (WorldCoherent)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using
  ( WorldCoherentWeakOneStepIndexedOutcome
  ; world-coherent-left-indexed-catchup
  ; world-indexed-outcome-source-blame
  )
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationBlameRootsDef
  using (WorldCoherentRightOneStepApplicationBlameRoots)
open import
  proof.WorldCoherent.Value.NuImprecisionWorldCoherentValueCatchupDef
  using (WorldCoherentLeftValueCatchupᵀ)


world-coherent-right-one-step-application-blame-roots-proofᵀ :
  WorldCoherentLeftValueCatchupᵀ →
  WorldCoherentRightOneStepApplicationBlameRoots
world-coherent-right-one-step-application-blame-roots-proofᵀ catchup =
  record
    { rightStepTargetApplicationLeftBlameRoot = left-blame
    ; rightStepTargetApplicationRightBlameRoot = right-blame
    }
  where
  left-blame :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {L M : Term} {A A′ B B′ : Ty}
      {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
    RuntimeOK (L · M) →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ L ⊑ blame
      ⦂ A ⇒ B ⊑ A′ ⇒ B′ ∶ pA ↦ pB →
    WorldCoherentWeakOneStepIndexedOutcome
      {M = L · M} {N′ = blame} {χ = keep} {ρ = ρ} pB
  left-blame (ok-no (no•-· noL noM)) L⊑blame
      with left-catchup-target-blameᵀ (ok-no noL) L⊑blame
  left-blame (ok-no (no•-· noL noM)) L⊑blame
      | χs , L↠blame =
    world-indexed-outcome-source-blame
      (·₁-blame-tail noM L↠blame)
  left-blame (ok-·₁ okL noM) L⊑blame
      with left-catchup-target-blameᵀ okL L⊑blame
  left-blame (ok-·₁ okL noM) L⊑blame
      | χs , L↠blame =
    world-indexed-outcome-source-blame
      (·₁-blame-tail noM L↠blame)
  left-blame (ok-·₂ vL noL okM) L⊑blame =
    ⊥-elim (value-not-target-blameᵀ vL L⊑blame)

  right-blame :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {L M V′ : Term} {A A′ B B′ : Ty}
      {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
    WorldCoherent ρ →
    SourceNameExclusive Φ →
    AssumptionMembershipUnique Φ →
    StoreWf Δᴸ (leftStoreⁱ ρ) →
    RuntimeOK (L · M) →
    Value V′ →
    No• V′ →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ L ⊑ V′
      ⦂ A ⇒ B ⊑ A′ ⇒ B′ ∶ pA ↦ pB →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ M ⊑ blame ⦂ A ⊑ A′ ∶ pA →
    WorldCoherentWeakOneStepIndexedOutcome
      {M = L · M} {N′ = blame} {χ = keep} {ρ = ρ} pB
  right-blame coherent exclusive unique wfL
      (ok-no (no•-· noL noM)) vV′ noV′ L⊑V′ M⊑blame
      with catchup coherent exclusive unique wfL
        (ok-no noL) vV′ noV′ L⊑V′
  right-blame coherent exclusive unique wfL
      (ok-no (no•-· noL noM)) vV′ noV′ L⊑V′ M⊑blame
      | world-coherent-left-indexed-catchup
          caught caught-lineage final-coherent final-exclusive final-unique
          final-wfL
      with sourceIsValueOrBlame (catchupIndexedInvariant caught)
  right-blame coherent exclusive unique wfL
      (ok-no (no•-· noL noM)) vV′ noV′ L⊑V′ M⊑blame
      | world-coherent-left-indexed-catchup
          caught caught-lineage final-coherent final-exclusive final-unique
          final-wfL
      | inj₂ refl =
    world-indexed-outcome-source-blame
      (·₁-blame-tail noM
        (sourceCatchup
          (weakIndexedResult (catchupIndexedResult caught))))
  right-blame coherent exclusive unique wfL
      (ok-no (no•-· noL noM)) vV′ noV′ L⊑V′ M⊑blame
      | world-coherent-left-indexed-catchup
          caught caught-lineage final-coherent final-exclusive final-unique
          final-wfL
      | inj₁ (vW , noW)
      with targetTailIsEmpty
        (silentInvariant (catchupIndexedInvariant caught))
  right-blame coherent exclusive unique wfL
      (ok-no (no•-· noL noM)) vV′ noV′ L⊑V′ M⊑blame
      | world-coherent-left-indexed-catchup
          caught caught-lineage final-coherent final-exclusive final-unique
          final-wfL
      | inj₁ (vW , noW) | refl
      with left-catchup-target-blameᵀ
        (ok-no
          (applyTerms-preserves-No•
            (sourceChanges
              (weakIndexedResult (catchupIndexedResult caught)))
            noM))
        (transportNo•Terms
          (weakIndexedTransport (catchupIndexedResult caught))
          noM no•-blame M⊑blame)
  right-blame coherent exclusive unique wfL
      (ok-no (no•-· noL noM)) vV′ noV′ L⊑V′ M⊑blame
      | world-coherent-left-indexed-catchup
          caught caught-lineage final-coherent final-exclusive final-unique
          final-wfL
      | inj₁ (vW , noW) | refl | χs , M↠blame =
    world-indexed-outcome-source-blame
      (↠-trans
        (·₁-↠ noM
          (sourceCatchup
            (weakIndexedResult (catchupIndexedResult caught))))
        (·₂-blame-tail vW noW M↠blame))
  right-blame coherent exclusive unique wfL
      (ok-·₁ okL noM) vV′ noV′ L⊑V′ M⊑blame
      with catchup coherent exclusive unique wfL
        okL vV′ noV′ L⊑V′
  right-blame coherent exclusive unique wfL
      (ok-·₁ okL noM) vV′ noV′ L⊑V′ M⊑blame
      | world-coherent-left-indexed-catchup
          caught caught-lineage final-coherent final-exclusive final-unique
          final-wfL
      with sourceIsValueOrBlame (catchupIndexedInvariant caught)
  right-blame coherent exclusive unique wfL
      (ok-·₁ okL noM) vV′ noV′ L⊑V′ M⊑blame
      | world-coherent-left-indexed-catchup
          caught caught-lineage final-coherent final-exclusive final-unique
          final-wfL
      | inj₂ refl =
    world-indexed-outcome-source-blame
      (·₁-blame-tail noM
        (sourceCatchup
          (weakIndexedResult (catchupIndexedResult caught))))
  right-blame coherent exclusive unique wfL
      (ok-·₁ okL noM) vV′ noV′ L⊑V′ M⊑blame
      | world-coherent-left-indexed-catchup
          caught caught-lineage final-coherent final-exclusive final-unique
          final-wfL
      | inj₁ (vW , noW)
      with targetTailIsEmpty
        (silentInvariant (catchupIndexedInvariant caught))
  right-blame coherent exclusive unique wfL
      (ok-·₁ okL noM) vV′ noV′ L⊑V′ M⊑blame
      | world-coherent-left-indexed-catchup
          caught caught-lineage final-coherent final-exclusive final-unique
          final-wfL
      | inj₁ (vW , noW) | refl
      with left-catchup-target-blameᵀ
        (ok-no
          (applyTerms-preserves-No•
            (sourceChanges
              (weakIndexedResult (catchupIndexedResult caught)))
            noM))
        (transportNo•Terms
          (weakIndexedTransport (catchupIndexedResult caught))
          noM no•-blame M⊑blame)
  right-blame coherent exclusive unique wfL
      (ok-·₁ okL noM) vV′ noV′ L⊑V′ M⊑blame
      | world-coherent-left-indexed-catchup
          caught caught-lineage final-coherent final-exclusive final-unique
          final-wfL
      | inj₁ (vW , noW) | refl | χs , M↠blame =
    world-indexed-outcome-source-blame
      (↠-trans
        (·₁-↠ noM
          (sourceCatchup
            (weakIndexedResult (catchupIndexedResult caught))))
        (·₂-blame-tail vW noW M↠blame))
  right-blame coherent exclusive unique wfL
      (ok-·₂ vL noL okM) vV′ noV′ L⊑V′ M⊑blame
      with left-catchup-target-blameᵀ okM M⊑blame
  right-blame coherent exclusive unique wfL
      (ok-·₂ vL noL okM) vV′ noV′ L⊑V′ M⊑blame
      | χs , M↠blame =
    world-indexed-outcome-source-blame
      (·₂-blame-tail vL noL M↠blame)

module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPrimitiveBlameRootsProof
  where

-- File Charter:
--   * Implements both target primitive-blame roots for world-coherent
--     target-oriented one-step simulation.
--   * Exhaustively separates source primitive terms whose left operand must
--     catch up from those whose left operand is already a value.
--   * Every branch constructs a source reduction sequence to blame.
--   * Contains no recursive dispatcher, postulate, hole, permissive option,
--     delta root, continuing related branch, or compatibility wrapper.

open import Agda.Builtin.Equality using (refl)
open import Data.Empty using (⊥-elim)
open import Data.List using ([]; _∷_; _++_)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import ImprecisionWf using
  ( ImpCtx
  ; idι
  )
open import NuReduction using
  ( keep
  ; applyTerms
  ; blame-⊕₁
  ; blame-⊕₂
  ; pure-step
  ; ↠-refl
  ; ↠-step
  ; _—↠[_]_
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
  ; no•-⊕
  ; ok-no
  ; ok-⊕₁
  ; ok-⊕₂
  ; _⊕[_]_
  )
open import Primitives using (addℕ)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using
  ( TyCtx
  ; `ℕ
  ; ‵_
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
  ( applyTerms-preserves-No•
  ; applyTerms-preserves-Value
  ; ⊕₁-↠
  ; ⊕₂-↠
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
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPrimitiveBlameRootsDef
  using (WorldCoherentRightOneStepPrimitiveBlameRoots)
open import
  proof.WorldCoherent.Value.NuImprecisionWorldCoherentValueCatchupDef
  using (WorldCoherentLeftValueCatchupᵀ)


private
  ⊕₁-blame-tail :
    ∀ {L M χs} →
    No• M →
    L —↠[ χs ] blame →
    L ⊕[ addℕ ] M —↠[ χs ++ keep ∷ [] ] blame
  ⊕₁-blame-tail noM L↠blame =
    ↠-trans (⊕₁-↠ noM L↠blame)
      (↠-step (pure-step blame-⊕₁) ↠-refl)

  ⊕₂-blame-tail :
    ∀ {L M χs} →
    Value L →
    No• L →
    M —↠[ χs ] blame →
    L ⊕[ addℕ ] M —↠[ χs ++ keep ∷ [] ] blame
  ⊕₂-blame-tail {χs = χs} vL noL M↠blame =
    ↠-trans (⊕₂-↠ vL noL M↠blame)
      (↠-step
        (pure-step
          (blame-⊕₂ (applyTerms-preserves-Value χs vL)))
        ↠-refl)


world-coherent-right-one-step-primitive-blame-roots-proofᵀ :
  WorldCoherentLeftValueCatchupᵀ →
  WorldCoherentRightOneStepPrimitiveBlameRoots
world-coherent-right-one-step-primitive-blame-roots-proofᵀ catchup =
  record
    { rightStepTargetPrimitiveLeftBlameRoot = left-blame
    ; rightStepTargetPrimitiveRightBlameRoot = right-blame
    }
  where
  left-blame :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {L M : Term} →
    RuntimeOK (L ⊕[ addℕ ] M) →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ L ⊑ blame ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι →
    WorldCoherentWeakOneStepIndexedOutcome
      {M = L ⊕[ addℕ ] M} {N′ = blame}
      {A = ‵ `ℕ} {B = ‵ `ℕ}
      {χ = keep} {ρ = ρ} idι
  left-blame (ok-no (no•-⊕ noL noM)) L⊑blame
      with left-catchup-target-blameᵀ (ok-no noL) L⊑blame
  left-blame (ok-no (no•-⊕ noL noM)) L⊑blame
      | χs , L↠blame =
    world-indexed-outcome-source-blame
      (⊕₁-blame-tail noM L↠blame)
  left-blame (ok-⊕₁ okL noM) L⊑blame
      with left-catchup-target-blameᵀ okL L⊑blame
  left-blame (ok-⊕₁ okL noM) L⊑blame
      | χs , L↠blame =
    world-indexed-outcome-source-blame
      (⊕₁-blame-tail noM L↠blame)
  left-blame (ok-⊕₂ vL noL okM) L⊑blame =
    ⊥-elim (value-not-target-blameᵀ vL L⊑blame)

  right-blame-after-left-catchup :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {L M V′ : Term} →
    WorldCoherent ρ →
    SourceNameExclusive Φ →
    AssumptionMembershipUnique Φ →
    StoreWf Δᴸ (leftStoreⁱ ρ) →
    RuntimeOK L →
    No• M →
    Value V′ →
    No• V′ →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ L ⊑ V′ ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ M ⊑ blame ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι →
    WorldCoherentWeakOneStepIndexedOutcome
      {M = L ⊕[ addℕ ] M} {N′ = blame}
      {A = ‵ `ℕ} {B = ‵ `ℕ}
      {χ = keep} {ρ = ρ} idι
  right-blame-after-left-catchup
      coherent exclusive unique wfL okL noM vV′ noV′ L⊑V′ M⊑blame
      with catchup coherent exclusive unique wfL
        okL vV′ noV′ L⊑V′
  right-blame-after-left-catchup
      coherent exclusive unique wfL okL noM vV′ noV′ L⊑V′ M⊑blame
      | world-coherent-left-indexed-catchup
          caught caught-lineage final-coherent final-exclusive final-unique
          final-wfL
      with sourceIsValueOrBlame (catchupIndexedInvariant caught)
  right-blame-after-left-catchup
      coherent exclusive unique wfL okL noM vV′ noV′ L⊑V′ M⊑blame
      | world-coherent-left-indexed-catchup
          caught caught-lineage final-coherent final-exclusive final-unique
          final-wfL
      | inj₂ refl =
    world-indexed-outcome-source-blame
      (⊕₁-blame-tail noM
        (sourceCatchup
          (weakIndexedResult (catchupIndexedResult caught))))
  right-blame-after-left-catchup
      coherent exclusive unique wfL okL noM vV′ noV′ L⊑V′ M⊑blame
      | world-coherent-left-indexed-catchup
          caught caught-lineage final-coherent final-exclusive final-unique
          final-wfL
      | inj₁ (vW , noW)
      with targetTailIsEmpty
        (silentInvariant (catchupIndexedInvariant caught))
  right-blame-after-left-catchup
      coherent exclusive unique wfL okL noM vV′ noV′ L⊑V′ M⊑blame
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
  right-blame-after-left-catchup
      coherent exclusive unique wfL okL noM vV′ noV′ L⊑V′ M⊑blame
      | world-coherent-left-indexed-catchup
          caught caught-lineage final-coherent final-exclusive final-unique
          final-wfL
      | inj₁ (vW , noW) | refl | χs , M↠blame =
    world-indexed-outcome-source-blame
      (↠-trans
        (⊕₁-↠ noM
          (sourceCatchup
            (weakIndexedResult (catchupIndexedResult caught))))
        (⊕₂-blame-tail vW noW M↠blame))

  right-blame :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {L M V′ : Term} →
    WorldCoherent ρ →
    SourceNameExclusive Φ →
    AssumptionMembershipUnique Φ →
    StoreWf Δᴸ (leftStoreⁱ ρ) →
    RuntimeOK (L ⊕[ addℕ ] M) →
    Value V′ →
    No• V′ →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ L ⊑ V′ ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ M ⊑ blame ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι →
    WorldCoherentWeakOneStepIndexedOutcome
      {M = L ⊕[ addℕ ] M} {N′ = blame}
      {A = ‵ `ℕ} {B = ‵ `ℕ}
      {χ = keep} {ρ = ρ} idι
  right-blame coherent exclusive unique wfL
      (ok-no (no•-⊕ noL noM)) vV′ noV′ L⊑V′ M⊑blame =
    right-blame-after-left-catchup
      coherent exclusive unique wfL
      (ok-no noL) noM vV′ noV′ L⊑V′ M⊑blame
  right-blame coherent exclusive unique wfL
      (ok-⊕₁ okL noM) vV′ noV′ L⊑V′ M⊑blame =
    right-blame-after-left-catchup
      coherent exclusive unique wfL
      okL noM vV′ noV′ L⊑V′ M⊑blame
  right-blame coherent exclusive unique wfL
      (ok-⊕₂ vL noL okM) vV′ noV′ L⊑V′ M⊑blame
      with left-catchup-target-blameᵀ okM M⊑blame
  right-blame coherent exclusive unique wfL
      (ok-⊕₂ vL noL okM) vV′ noV′ L⊑V′ M⊑blame
      | χs , M↠blame =
    world-indexed-outcome-source-blame
      (⊕₂-blame-tail vL noL M↠blame)

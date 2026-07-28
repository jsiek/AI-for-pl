module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPairedOuterCastRootsProof
  where

-- File Charter:
--   * Assembles the four paired outer-cast one-step cells.
--   * Proves the direct `conv⊑convᵀ` target-blame root without a separate
--     semantic capability.
--   * Decides source inertness for ordinary PairedCast roots, while retaining
--     the distinct prefix-aware quotient frame and active-value boundaries.
--   * Contains no implementation of either active synchronization boundary,
--     QTIP recursion, dispatcher, postulate, hole, or permissive option.

open import Coercions using (Coercion)
open import Data.List using ([])
open import Data.Product using (_,_)
open import Relation.Nullary using (yes; no)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuReduction using (keep; _—→_)
open import NuStore using (StoreWf)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using
  (RuntimeOK; Term; Value; blame; _⟨_⟩)
open import QuotientedTermImprecision using
  ( PairedCast
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Types using (Ty; TyCtx)
open import proof.Core.Properties.CoercionProperties using (inert-dec)
open import proof.DGG.Core.NuPreservation using (runtime-⟨⟩)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using (AssumptionMembershipUnique)
open import
  proof.NuCore.Relations.NuImprecisionContextExclusivityDef
  using (SourceNameExclusive)
open import proof.Target.Core.NuImprecisionTargetBlameCatchup using
  (cast-blame-tailᵀ; left-catchup-target-blameᵀ)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef
  using (WorldCoherent)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using
  ( WorldCoherentWeakOneStepIndexedOutcome
  ; world-indexed-outcome-source-blame
  )
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPairedCastFrameProof
  using (world-coherent-right-one-step-paired-cast-frame-proofᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPairedOuterCastRootsDef
  using (WorldCoherentRightOneStepPairedOuterCastRoots)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPairedSourceActiveValueRootDef
  using (WorldCoherentRightOneStepPairedSourceActiveValueRootᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPairedSourceInertValueRootDef
  using (WorldCoherentRightOneStepPairedSourceInertValueRootᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepQuotientActiveValueSynchronizationDef
  using (WorldCoherentRightOneStepQuotientActiveValueSynchronizationᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepQuotientFrameRecursionDef
  using (WorldCoherentRightOneStepQuotientFrameRecursionᵀ)


private
  paired-value-root :
    WorldCoherentRightOneStepPairedSourceInertValueRootᵀ →
    WorldCoherentRightOneStepPairedSourceActiveValueRootᵀ →
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {M V′ N′ : Term} {A A′ B B′ : Ty}
      {c c′ : Coercion}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
    WorldCoherent ρ →
    SourceNameExclusive Φ →
    AssumptionMembershipUnique Φ →
    StoreWf Δᴸ (leftStoreⁱ ρ) →
    StoreWf Δᴿ (rightStoreⁱ ρ) →
    RuntimeOK (M ⟨ c ⟩) →
    RuntimeOK (V′ ⟨ c′ ⟩) →
    Value V′ →
    PairedCast Φ Δᴸ Δᴿ ρ c c′ p q →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ M ⊑ V′ ⦂ A ⊑ A′ ∶ p →
    V′ ⟨ c′ ⟩ —→ N′ →
    WorldCoherentWeakOneStepIndexedOutcome
      {M = M ⟨ c ⟩} {N′ = N′}
      {χ = keep} {ρ = ρ} q
  paired-value-root
      inert-root active-root coherent exclusive unique wfL wfR
      ok-source ok-target vV′ paired M⊑V′ target-root
      with inert-dec _
  paired-value-root
      inert-root active-root coherent exclusive unique wfL wfR
      ok-source ok-target vV′ paired M⊑V′ target-root
      | yes inert =
    inert-root coherent exclusive unique wfL wfR
      ok-source ok-target vV′ inert paired M⊑V′ target-root
  paired-value-root
      inert-root active-root coherent exclusive unique wfL wfR
      ok-source ok-target vV′ paired M⊑V′ target-root
      | no noninert =
    active-root coherent exclusive unique wfL wfR
      ok-source ok-target vV′ noninert paired M⊑V′ target-root


world-coherent-right-one-step-paired-target-blame-rootᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ}
    {M : Term} {A A′ B B′ : Ty} {c c′ : Coercion}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  RuntimeOK (M ⟨ c ⟩) →
  PairedCast Φ Δᴸ Δᴿ ρᵇ c c′ p q →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρᵇ ∣ []
    ⊢ᴺ M ⊑ blame ⦂ A ⊑ A′ ∶ p →
  WorldCoherentWeakOneStepIndexedOutcome
    {M = M ⟨ c ⟩} {N′ = blame}
    {χ = keep} {ρ = ρ} q
world-coherent-right-one-step-paired-target-blame-rootᵀ
    ok-source paired M⊑blame
    with left-catchup-target-blameᵀ
      (runtime-⟨⟩ ok-source) M⊑blame
world-coherent-right-one-step-paired-target-blame-rootᵀ
    ok-source paired M⊑blame
    | χs , M↠blame =
  world-indexed-outcome-source-blame
    (cast-blame-tailᵀ M↠blame)


world-coherent-right-one-step-paired-outer-cast-roots-proofᵀ :
  WorldCoherentRightOneStepPairedSourceInertValueRootᵀ →
  WorldCoherentRightOneStepPairedSourceActiveValueRootᵀ →
  WorldCoherentRightOneStepQuotientFrameRecursionᵀ →
  WorldCoherentRightOneStepQuotientActiveValueSynchronizationᵀ →
  WorldCoherentRightOneStepPairedOuterCastRoots
world-coherent-right-one-step-paired-outer-cast-roots-proofᵀ
    inert-root active-root quotient-frame quotient-active =
  record
    { rightStepPairedCastFrame =
        world-coherent-right-one-step-paired-cast-frame-proofᵀ
    ; rightStepPairedCastValueRoot =
        paired-value-root inert-root active-root
    ; rightStepQuotientWideningFrame = quotient-frame
    ; rightStepQuotientWideningValueRoot = quotient-active
    }

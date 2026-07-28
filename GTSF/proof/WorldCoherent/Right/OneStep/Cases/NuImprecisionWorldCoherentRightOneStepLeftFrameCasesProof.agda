module
  proof.WorldCoherent.Right.OneStep.Cases.NuImprecisionWorldCoherentRightOneStepLeftFrameCasesProof
  where

-- File Charter:
--   * Proves the application-left and primitive-left target-step dispatcher
--     clauses for both no-bullet and active-source-right runtime shapes.
--   * Recurses in the no-bullet branch and uses value catch-up plus indexed
--     residualization in the value-left/runtime-right branch.
--   * Contains no recursive dispatcher implementation, result wrapper,
--     postulate, hole, permissive option, or compatibility alias.

open import Data.List using ([])
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)

open import ImprecisionWf using
  ( ImpCtx
  ; idι
  ; _↦_
  ; _∣_⊢_⊑_⊣_
  )
open import NuReduction using
  ( StoreChange
  ; applyTerm
  ; _—→[_]_
  )
open import NuStore using (StoreWf)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using
  ( RuntimeOK
  ; Term
  ; _·_
  ; _⊕[_]_
  )
open import Primitives using (addℕ)
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; allocation-prefixᵀ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using
  (_∣_∣_⊢_⦂_)
open import Types using
  ( Ty
  ; TyCtx
  ; `ℕ
  ; ‵_
  ; _⇒_
  )
open import
  proof.Catchup.Simulation.NuImprecisionSimulationCore
  using (runtime-application-left-view)
open import proof.DGG.Core.NuPreservation using
  (runtime-·₁; runtime-⊕₁)
open import proof.OneStep.NuImprecisionOneStepPrimitiveLeaves using
  (runtime-⊕₁-viewᵀ)
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
  using (WorldCoherentWeakOneStepIndexedOutcome)
open import
  proof.WorldCoherent.Right.OneStep.Cases.NuImprecisionWorldCoherentRightOneStepPrefixDef
  using (WorldCoherentWeakOneStepIndexedSimulationPrefixᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Cases.NuImprecisionWorldCoherentRightOneStepResidualLeftFramesProof
  using
  ( world-coherent-right-one-step-residual-application-left-frameᵀ
  ; world-coherent-right-one-step-residual-primitive-left-frameᵀ
  )
open import
  proof.WorldCoherent.Right.OneStep.Frames.NuImprecisionWorldCoherentRightOneStepApplicationFramesDef
  using
  ( WorldCoherentRightOneStepApplicationFrames
  ; rightStepApplicationLeftFrame
  )
open import
  proof.WorldCoherent.Right.OneStep.Frames.NuImprecisionWorldCoherentRightOneStepPrimitiveFramesDef
  using
  ( WorldCoherentRightOneStepPrimitiveFrames
  ; rightStepPrimitiveLeftFrame
  )
open import
  proof.WorldCoherent.Right.Target.Framing.NuImprecisionWorldCoherentRightTargetIndexedStepResidualProof
  using (world-coherent-right-target-indexed-step-residual-proofᵀ)
open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightValueCatchupPrefixDef
  using (WorldCoherentRightValueCatchupPrefixᵀ)
open import
  proof.WorldCoherent.Right.Value.Transport.NuImprecisionWorldCoherentRightValueCatchupRuntimeNoBulletTransportDef
  using (WorldCoherentRightValueCatchupRuntimeNoBulletTransportᵀ)


world-coherent-right-one-step-application-left-caseᵀ :
  WorldCoherentWeakOneStepIndexedSimulationPrefixᵀ →
  WorldCoherentRightValueCatchupPrefixᵀ →
  WorldCoherentRightValueCatchupRuntimeNoBulletTransportᵀ →
  WorldCoherentRightOneStepApplicationFrames →
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ}
    {L L′ L₁′ M M′ : Term} {A A′ B B′ : Ty}
    {χ : StoreChange}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρᵇ ρ →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  RuntimeOK (L · M) →
  RuntimeOK (L′ · M′) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρᵇ ∣ []
    ⊢ᴺ L ⊑ L′
      ⦂ A ⇒ B ⊑ A′ ⇒ B′ ∶ pA ↦ pB →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρᵇ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ A ⊑ A′ ∶ pA →
  Δᴸ ∣ leftStoreⁱ ρ ∣ [] ⊢ L ⦂ A ⇒ B →
  Δᴸ ∣ leftStoreⁱ ρ ∣ [] ⊢ M ⦂ A →
  Δᴿ ∣ rightStoreⁱ ρ ∣ [] ⊢ L′ ⦂ A′ ⇒ B′ →
  Δᴿ ∣ rightStoreⁱ ρ ∣ [] ⊢ M′ ⦂ A′ →
  L′ —→[ χ ] L₁′ →
  WorldCoherentWeakOneStepIndexedOutcome
    {M = L · M} {N′ = L₁′ · applyTerm χ M′}
    {A = B} {B = B′} {χ = χ} {ρ = ρ} pB
world-coherent-right-one-step-application-left-caseᵀ
    recursive catchup runtime-transport frames
    prefix coherent exclusive unique wfL wfR okLM okL′M′
    L⊑L′ M⊑M′ L⊢ M⊢ L′⊢ M′⊢ L′→
    with runtime-application-left-view okLM okL′M′ L′→
world-coherent-right-one-step-application-left-caseᵀ
    recursive catchup runtime-transport frames
    prefix coherent exclusive unique wfL wfR okLM okL′M′
    L⊑L′ M⊑M′ L⊢ M⊢ L′⊢ M′⊢ L′→
    | inj₁ (noM , noM′) =
  rightStepApplicationLeftFrame frames noM noM′
    (allocation-prefixᵀ prefix M⊑M′ M⊢ M′⊢)
    (recursive prefix coherent exclusive unique wfL wfR
      (runtime-·₁ okLM) (runtime-·₁ okL′M′)
      L⊑L′ L⊢ L′⊢ L′→)
world-coherent-right-one-step-application-left-caseᵀ
    recursive catchup runtime-transport frames
    prefix coherent exclusive unique wfL wfR okLM okL′M′
    L⊑L′ M⊑M′ L⊢ M⊢ L′⊢ M′⊢ L′→
    | inj₂ (vL , noL , okM , noM′) =
  world-coherent-right-one-step-residual-application-left-frameᵀ
    prefix okM noM′ M⊢ M⊑M′
    (world-coherent-right-target-indexed-step-residual-proofᵀ
      runtime-transport L′→
      (catchup prefix coherent exclusive unique wfR
        (runtime-·₁ okL′M′) vL noL L⊑L′))


world-coherent-right-one-step-primitive-left-caseᵀ :
  WorldCoherentWeakOneStepIndexedSimulationPrefixᵀ →
  WorldCoherentRightValueCatchupPrefixᵀ →
  WorldCoherentRightValueCatchupRuntimeNoBulletTransportᵀ →
  WorldCoherentRightOneStepPrimitiveFrames →
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ}
    {L L′ L₁′ M M′ : Term} {χ : StoreChange} →
  StoreImpPrefix ρᵇ ρ →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  RuntimeOK (L ⊕[ addℕ ] M) →
  RuntimeOK (L′ ⊕[ addℕ ] M′) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρᵇ ∣ []
    ⊢ᴺ L ⊑ L′ ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρᵇ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι →
  Δᴸ ∣ leftStoreⁱ ρ ∣ [] ⊢ L ⦂ ‵ `ℕ →
  Δᴸ ∣ leftStoreⁱ ρ ∣ [] ⊢ M ⦂ ‵ `ℕ →
  Δᴿ ∣ rightStoreⁱ ρ ∣ [] ⊢ L′ ⦂ ‵ `ℕ →
  Δᴿ ∣ rightStoreⁱ ρ ∣ [] ⊢ M′ ⦂ ‵ `ℕ →
  L′ —→[ χ ] L₁′ →
  WorldCoherentWeakOneStepIndexedOutcome
    {M = L ⊕[ addℕ ] M}
    {N′ = L₁′ ⊕[ addℕ ] applyTerm χ M′}
    {A = ‵ `ℕ} {B = ‵ `ℕ} {χ = χ} {ρ = ρ} idι
world-coherent-right-one-step-primitive-left-caseᵀ
    recursive catchup runtime-transport frames
    prefix coherent exclusive unique wfL wfR okLM okL′M′
    L⊑L′ M⊑M′ L⊢ M⊢ L′⊢ M′⊢ L′→
    with runtime-⊕₁-viewᵀ okLM okL′M′ L′→
world-coherent-right-one-step-primitive-left-caseᵀ
    recursive catchup runtime-transport frames
    prefix coherent exclusive unique wfL wfR okLM okL′M′
    L⊑L′ M⊑M′ L⊢ M⊢ L′⊢ M′⊢ L′→
    | inj₁ (noM , noM′) =
  rightStepPrimitiveLeftFrame frames noM noM′
    (allocation-prefixᵀ prefix M⊑M′ M⊢ M′⊢)
    (recursive prefix coherent exclusive unique wfL wfR
      (runtime-⊕₁ okLM) (runtime-⊕₁ okL′M′)
      L⊑L′ L⊢ L′⊢ L′→)
world-coherent-right-one-step-primitive-left-caseᵀ
    recursive catchup runtime-transport frames
    prefix coherent exclusive unique wfL wfR okLM okL′M′
    L⊑L′ M⊑M′ L⊢ M⊢ L′⊢ M′⊢ L′→
    | inj₂ (vL , noL , okM , noM′) =
  world-coherent-right-one-step-residual-primitive-left-frameᵀ
    prefix okM noM′ M⊢ M⊑M′
    (world-coherent-right-target-indexed-step-residual-proofᵀ
      runtime-transport L′→
      (catchup prefix coherent exclusive unique wfR
        (runtime-⊕₁ okL′M′) vL noL L⊑L′))

module
  proof.WorldCoherent.Right.OneStep.Cases.NuImprecisionWorldCoherentRightOneStepRightFrameValueCasesProof
  where

-- File Charter:
--   * Proves the application-right and primitive-right target-step dispatcher
--     clauses when both left operands are already bullet-free values.
--   * Weakens the left-operand relation to the ambient store and delegates
--     right-operand simulation to the recursive dispatcher.
--   * Contains no catch-up, crossed runtime case, result wrapper, postulate,
--     hole, permissive option, or compatibility alias.

open import Data.List using ([])

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
open import NuTermImprecision using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; Term
  ; Value
  ; _·_
  ; _⊕[_]_
  )
open import Primitives using (addℕ)
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; allocation-prefixᵀ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using (_∣_∣_⊢_⦂_)
open import Types using
  ( Ty
  ; TyCtx
  ; `ℕ
  ; ‵_
  ; _⇒_
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
  using (WorldCoherentWeakOneStepIndexedOutcome)
open import
  proof.WorldCoherent.Right.OneStep.Cases.NuImprecisionWorldCoherentRightOneStepPrefixDef
  using (WorldCoherentWeakOneStepIndexedSimulationPrefixᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Frames.NuImprecisionWorldCoherentRightOneStepApplicationFramesDef
  using
  ( WorldCoherentRightOneStepApplicationFrames
  ; rightStepApplicationRightFrame
  )
open import
  proof.WorldCoherent.Right.OneStep.Frames.NuImprecisionWorldCoherentRightOneStepPrimitiveFramesDef
  using
  ( WorldCoherentRightOneStepPrimitiveFrames
  ; rightStepPrimitiveRightFrame
  )


world-coherent-right-one-step-application-right-value-caseᵀ :
  WorldCoherentWeakOneStepIndexedSimulationPrefixᵀ →
  WorldCoherentRightOneStepApplicationFrames →
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ}
    {L L′ M M′ M₁′ : Term} {A A′ B B′ : Ty}
    {χ : StoreChange}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρᵇ ρ →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  Value L →
  No• L →
  Value L′ →
  No• L′ →
  RuntimeOK M →
  RuntimeOK M′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρᵇ ∣ []
    ⊢ᴺ L ⊑ L′
      ⦂ A ⇒ B ⊑ A′ ⇒ B′ ∶ pA ↦ pB →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρᵇ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ A ⊑ A′ ∶ pA →
  Δᴸ ∣ leftStoreⁱ ρ ∣ [] ⊢ L ⦂ A ⇒ B →
  Δᴸ ∣ leftStoreⁱ ρ ∣ [] ⊢ M ⦂ A →
  Δᴿ ∣ rightStoreⁱ ρ ∣ [] ⊢ L′ ⦂ A′ ⇒ B′ →
  Δᴿ ∣ rightStoreⁱ ρ ∣ [] ⊢ M′ ⦂ A′ →
  M′ —→[ χ ] M₁′ →
  WorldCoherentWeakOneStepIndexedOutcome
    {M = L · M} {N′ = applyTerm χ L′ · M₁′}
    {A = B} {B = B′} {χ = χ} {ρ = ρ} pB
world-coherent-right-one-step-application-right-value-caseᵀ
    recursive frames prefix coherent exclusive unique wfL wfR
    vL noL vL′ noL′ okM okM′ L⊑L′ M⊑M′
    L⊢ M⊢ L′⊢ M′⊢ M′→ =
  rightStepApplicationRightFrame frames vL noL vL′ noL′
    (allocation-prefixᵀ prefix L⊑L′ L⊢ L′⊢)
    (recursive prefix coherent exclusive unique wfL wfR
      okM okM′ M⊑M′ M⊢ M′⊢ M′→)


world-coherent-right-one-step-primitive-right-value-caseᵀ :
  WorldCoherentWeakOneStepIndexedSimulationPrefixᵀ →
  WorldCoherentRightOneStepPrimitiveFrames →
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ}
    {L L′ M M′ M₁′ : Term} {χ : StoreChange} →
  StoreImpPrefix ρᵇ ρ →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  Value L →
  No• L →
  Value L′ →
  No• L′ →
  RuntimeOK M →
  RuntimeOK M′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρᵇ ∣ []
    ⊢ᴺ L ⊑ L′ ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρᵇ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι →
  Δᴸ ∣ leftStoreⁱ ρ ∣ [] ⊢ L ⦂ ‵ `ℕ →
  Δᴸ ∣ leftStoreⁱ ρ ∣ [] ⊢ M ⦂ ‵ `ℕ →
  Δᴿ ∣ rightStoreⁱ ρ ∣ [] ⊢ L′ ⦂ ‵ `ℕ →
  Δᴿ ∣ rightStoreⁱ ρ ∣ [] ⊢ M′ ⦂ ‵ `ℕ →
  M′ —→[ χ ] M₁′ →
  WorldCoherentWeakOneStepIndexedOutcome
    {M = L ⊕[ addℕ ] M}
    {N′ = applyTerm χ L′ ⊕[ addℕ ] M₁′}
    {A = ‵ `ℕ} {B = ‵ `ℕ} {χ = χ} {ρ = ρ} idι
world-coherent-right-one-step-primitive-right-value-caseᵀ
    recursive frames prefix coherent exclusive unique wfL wfR
    vL noL vL′ noL′ okM okM′ L⊑L′ M⊑M′
    L⊢ M⊢ L′⊢ M′⊢ M′→ =
  rightStepPrimitiveRightFrame frames vL noL vL′ noL′
    (allocation-prefixᵀ prefix L⊑L′ L⊢ L′⊢)
    (recursive prefix coherent exclusive unique wfL wfR
      okM okM′ M⊑M′ M⊢ M′⊢ M′→)

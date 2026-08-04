module
  proof.DGG.TerminalBackward.NuDGGTerminalBackwardBlameWorldCoherentProof
  where

-- File Charter:
--   * Proves backward target-blame trace simulation from the strict
--     world-coherent target-oriented one-step contract.
--   * Threads world coherence, source-name exclusivity, and assumption-name
--     uniqueness through every continuing result.
--   * Exposes the direct closed-world specialization consumed by terminal DGG.
--   * Contains no permissive dispatcher, postulate, hole, or theorem alias.

open import Data.List using ([]; _∷_; _++_; length)
open import Data.Nat using (ℕ; zero; suc; s≤s⁻¹; _≤_)
open import Data.Nat.Properties using (≤-refl; ≤-trans)
open import Data.Product using (_,_; ∃-syntax)

open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuReduction using
  ( StoreChanges
  ; ↠-refl
  ; ↠-step
  ; _—↠[_]_
  )
open import NuStore using (StoreWf)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using (RuntimeOK; blame)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import proof.Core.Properties.ReductionProperties using (↠-trans)
open import proof.DGG.Core.NuDGGClosedWorld using
  (empty-store-wf; empty-world-coherent)
open import proof.DGG.Core.NuDGGTraceAlignment using
  (weak-result-target-prefix-blameᵀ)
open import proof.DGG.Core.NuDGGTraceMeasure using
  (aligned-residual-shorter)
open import proof.DGG.Core.NuDGGWeakResultPreservation using
  ( weak-result-source-store-wf
  ; weak-result-source-runtime
  ; weak-result-target-store-wf
  ; weak-result-target-runtime
  )
open import proof.DGG.TerminalBackward.NuDGGTerminalBackwardValueProof using
  (empty-context-source-typing; empty-context-target-typing)
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  ( canonicalIndexedResults
  ; sourceCatchup
  ; sourceChanges
  ; targetTailChanges
  ; weakIndexedResult
  )
open import proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using (AssumptionMembershipUnique)
open import proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessProof
  using (assumption-membership-unique-empty)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityProof using
  (source-name-exclusive-empty)
open import proof.Target.Core.NuImprecisionTargetBlameCatchup using
  (left-catchup-target-blameᵀ)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherentOneStepDef using
  (WorldCoherentWeakOneStepIndexedSimulationᵀ)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef using
  ( WorldCoherentWeakOneStepIndexedOutcome
  ; world-indexed-outcome-related
  ; world-indexed-outcome-source-blame
  )


world-coherent-backward-target-blame-proofᵀ :
  WorldCoherentWeakOneStepIndexedSimulationᵀ →
  ∀ {Φ Δᴸ Δᴿ M M′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  RuntimeOK M →
  RuntimeOK M′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
  ∀ χs′ →
  M′ —↠[ χs′ ] blame →
  ∃[ χs ] (M —↠[ χs ] blame)
world-coherent-backward-target-blame-proofᵀ
    one-step coherent exclusive unique wfL wfR okM okM′ M⊑M′
    χs′ M′↠blame =
  go (length χs′) coherent exclusive unique wfL wfR okM okM′ M⊑M′
    χs′ M′↠blame ≤-refl
  where
  go :
    ∀ (fuel : ℕ) {Φ Δᴸ Δᴿ M M′ A B}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    WorldCoherent ρ →
    SourceNameExclusive Φ →
    AssumptionMembershipUnique Φ →
    StoreWf Δᴸ (leftStoreⁱ ρ) →
    StoreWf Δᴿ (rightStoreⁱ ρ) →
    RuntimeOK M →
    RuntimeOK M′ →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
    ∀ (ψs : StoreChanges) →
    M′ —↠[ ψs ] blame →
    length ψs ≤ fuel →
    ∃[ χs ] (M —↠[ χs ] blame)
  go zero coherent exclusive unique wfL wfR okM okM′ M⊑M′
      [] ↠-refl bound =
    left-catchup-target-blameᵀ okM M⊑M′
  go zero coherent exclusive unique wfL wfR okM okM′ M⊑M′
      (χ ∷ ψs) (↠-step target-step target-rest) ()
  go (suc fuel) coherent exclusive unique wfL wfR okM okM′ M⊑M′
      [] ↠-refl bound =
    left-catchup-target-blameᵀ okM M⊑M′
  go (suc fuel) coherent exclusive unique wfL wfR okM okM′ M⊑M′
      (χ ∷ ψs) (↠-step target-step target-rest) bound
    with one-step coherent exclusive unique wfL wfR okM okM′
      M⊑M′ target-step
  go (suc fuel) coherent exclusive unique wfL wfR okM okM′ M⊑M′
      (χ ∷ ψs) (↠-step target-step target-rest) bound
    | world-indexed-outcome-source-blame
        {χs = source-blame-changes} source-blame =
      source-blame-changes , source-blame
  go (suc fuel) coherent exclusive unique wfL wfR okM okM′ M⊑M′
      (χ ∷ ψs) (↠-step target-step target-rest) bound
    | world-indexed-outcome-related
        indexed successor-lineage successor-coherent successor-exclusive successor-unique
    with weak-result-target-prefix-blameᵀ
      (weakIndexedResult indexed) target-rest
  go (suc fuel) coherent exclusive unique wfL wfR okM okM′ M⊑M′
      (χ ∷ ψs) (↠-step target-step target-rest) bound
    | world-indexed-outcome-related
        indexed successor-lineage successor-coherent successor-exclusive successor-unique
    | residual-changes , target-result↠blame , trace-eq
    with go fuel successor-coherent successor-exclusive successor-unique
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
      residual-changes target-result↠blame
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
  go (suc fuel) coherent exclusive unique wfL wfR okM okM′ M⊑M′
      (χ ∷ ψs) (↠-step target-step target-rest) bound
    | world-indexed-outcome-related
        indexed successor-lineage successor-coherent successor-exclusive successor-unique
    | residual-changes , target-result↠blame , trace-eq
    | result-blame-changes , source-result↠blame =
      sourceChanges (weakIndexedResult indexed) ++ result-blame-changes ,
      ↠-trans (sourceCatchup (weakIndexedResult indexed))
              source-result↠blame


world-coherent-backward-target-blame-closed-proofᵀ :
  WorldCoherentWeakOneStepIndexedSimulationᵀ →
  ∀ {N N′ A B} {p : [] ∣ 0 ⊢ A ⊑ B ⊣ 0} →
  RuntimeOK N →
  RuntimeOK N′ →
  [] ∣ 0 ∣ 0 ∣ [] ∣ []
    ⊢ᴺ N ⊑ N′ ⦂ A ⊑ B ∶ p →
  ∀ χs′ →
  N′ —↠[ χs′ ] blame →
  ∃[ χs ] (N —↠[ χs ] blame)
world-coherent-backward-target-blame-closed-proofᵀ one-step =
  world-coherent-backward-target-blame-proofᵀ one-step
    empty-world-coherent source-name-exclusive-empty
    assumption-membership-unique-empty empty-store-wf empty-store-wf

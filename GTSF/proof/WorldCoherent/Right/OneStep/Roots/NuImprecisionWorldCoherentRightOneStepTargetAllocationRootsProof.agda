module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepTargetAllocationRootsProof
  where

-- File Charter:
--   * Proves the matched reveal-ν target-allocation root for world-coherent
--     target-oriented one-step simulation.
--   * Catches up the source before matched allocation, stops immediately on
--     source blame, and preserves relational-store lineage through allocation.
--   * Contains no recursive dispatcher, postulate, hole, permissive option,
--     or `blame-ν` root.

open import Agda.Builtin.Equality using (refl)
open import Conversion using (RevealConversion)
open import ConversionIndexCompatibility using
  (_[_↦_⊑⟨_⟩_↤_]ᴾ_)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)

open import ImprecisionWf using
  ( ImpCtx
  ; _ˣ⊑ˣ_
  ; _∣_⊢_⊑_⊣_
  ; ∀ⁱ_
  ; ⇑ᵢ
  )
open import NuReduction using
  ( bind
  ; blame-ν
  ; ↠-refl
  ; ↠-step
  )
open import NuStore using (StoreWf)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; Term
  ; Value
  ; no•-ν
  ; ok-no
  ; ok-ν
  ; ν
  ; ⇑ᵗᵐ
  ; _•
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using
  ( Ty
  ; TyCtx
  ; WfTy
  ; `∀
  ; ⇑ᵗ
  ; ⟰ᵗ
  )
open import proof.Core.Properties.NuImprecisionIndexedRenamingProperties using
  (∀ᵢᶜ; ⊑-lift∀ᵢ)
open import proof.Core.Properties.ReductionProperties using (ν-↠; ↠-trans)
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  ( left-catchup-invariant
  ; left-indexed-all-catchup
  ; left-indexed-catchup
  ; left-silent-invariant
  ; sourceCatchup
  ; weakIndexedResult
  )
open import
  proof.WorldCoherent.Right.OneStep.Allocation.NuImprecisionWorldCoherentMatchedNuAllocationAfterValueCatchupDef
  using (WorldCoherentMatchedNuAllocationAfterValueCatchupᵀ)
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
  proof.WorldCoherent.Value.NuImprecisionWorldCoherentValueCatchupDef
  using (WorldCoherentLeftValueCatchupᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepTargetAllocationRootsDef
  using (WorldCoherentRightOneStepTargetAllocationRoots)


ν-runtime : ∀ {A N s} → RuntimeOK (ν A N s) → RuntimeOK N
ν-runtime (ok-no (no•-ν no-N)) = ok-no no-N
ν-runtime (ok-ν ok-N) = ok-N


matched-nu-allocation :
  WorldCoherentMatchedNuAllocationAfterValueCatchupᵀ →
  WorldCoherentLeftValueCatchupᵀ →
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {A A′ B B′ C C′ : Ty} {N V′ : Term}
    {s s′} {μ μ′}
    {q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ}
    {A⇑⊑A′⇑ : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ ⇑ᵗ A ⊑ ⇑ᵗ A′ ⊣ suc Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  (pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ) →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  RuntimeOK (ν A N s) →
  Value V′ →
  No• V′ →
  WfTy Δᴸ A →
  WfTy Δᴿ A′ →
  RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ))
    zero (⇑ᵗ A) s C (⇑ᵗ B) →
  RevealConversion μ′ (suc Δᴿ)
    ((zero , ⇑ᵗ A′) ∷ ⟰ᵗ (rightStoreⁱ ρ))
    zero (⇑ᵗ A′) s′ C′ (⇑ᵗ B′) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ N ⊑ V′ ⦂ `∀ C ⊑ `∀ C′ ∶ ∀ⁱ q →
  q
    [ zero ↦ ⇑ᵗ A
    ⊑⟨ A⇑⊑A′⇑ ⟩
    ⇑ᵗ A′ ↤ zero ]ᴾ
    ⊑-lift∀ᵢ pB →
  WorldCoherentWeakOneStepIndexedOutcome
    {M = ν A N s} {N′ = ((⇑ᵗᵐ V′) •) ⟨ s′ ⟩}
    {χ = bind A′} {ρ = ρ} pB
matched-nu-allocation
    allocation catchup {A⇑⊑A′⇑ = A⇑⊑A′⇑} {pB = pB} pA
    coherent exclusive unique wfL wfR ok-source vV′ noV′ hA hA′
    s↑ s′↑ N⊑V′ replace
    with catchup coherent exclusive unique wfL
      (ν-runtime ok-source) vV′ noV′ N⊑V′
matched-nu-allocation
    allocation catchup {A⇑⊑A′⇑ = A⇑⊑A′⇑} {pB = pB} pA
    coherent exclusive unique wfL wfR ok-source vV′ noV′ hA hA′
    s↑ s′↑ N⊑V′ replace
    | world-coherent-left-indexed-catchup
        (left-indexed-catchup indexed
          (left-catchup-invariant
            (left-silent-invariant refl refl) final))
        caught-lineage final-coherent final-exclusive final-unique
        final-wfL
    with final
matched-nu-allocation
    allocation catchup {A⇑⊑A′⇑ = A⇑⊑A′⇑} {pB = pB} pA
    coherent exclusive unique wfL wfR ok-source vV′ noV′ hA hA′
    s↑ s′↑ N⊑V′ replace
    | world-coherent-left-indexed-catchup
        (left-indexed-catchup indexed
          (left-catchup-invariant
            (left-silent-invariant refl refl) final))
        caught-lineage final-coherent final-exclusive final-unique
        final-wfL
    | inj₂ refl =
  world-indexed-outcome-source-blame
    (↠-trans
      (ν-↠ (sourceCatchup (weakIndexedResult indexed)))
      (↠-step blame-ν ↠-refl))
matched-nu-allocation
    allocation catchup {A⇑⊑A′⇑ = A⇑⊑A′⇑} {pB = pB} pA
    coherent exclusive unique wfL wfR ok-source vV′ noV′ hA hA′
    s↑ s′↑ N⊑V′ replace
    | world-coherent-left-indexed-catchup
        (left-indexed-catchup indexed
          (left-catchup-invariant
            (left-silent-invariant refl refl) final))
        caught-lineage final-coherent final-exclusive final-unique
        final-wfL
    | inj₁ (vW , noW)
    =
  allocation s↑ s′↑ pA A⇑⊑A′⇑ pB replace vV′ noV′
    caught-all vW noW caught-lineage
    final-coherent final-exclusive final-unique
  where
  caught-all =
    left-indexed-all-catchup indexed
      (left-catchup-invariant
        (left-silent-invariant refl refl) (inj₁ (vW , noW)))


world-coherent-right-one-step-target-allocation-roots-proofᵀ :
  WorldCoherentMatchedNuAllocationAfterValueCatchupᵀ →
  WorldCoherentLeftValueCatchupᵀ →
  WorldCoherentRightOneStepTargetAllocationRoots
world-coherent-right-one-step-target-allocation-roots-proofᵀ
    allocation catchup =
  record
    { rightStepMatchedNuAllocationRoot =
        λ pA coherent exclusive unique wfL wfR ok-source
          vV′ noV′ hA hA′ s↑ s′↑ N⊑V′ replace →
          matched-nu-allocation allocation catchup pA
            coherent exclusive unique wfL wfR ok-source
            vV′ noV′ hA hA′ s↑ s′↑ N⊑V′ replace
    }

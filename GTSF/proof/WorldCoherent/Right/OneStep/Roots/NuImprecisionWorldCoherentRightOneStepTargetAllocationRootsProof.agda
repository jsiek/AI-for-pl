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
import CastImprecisionShape as CastShape
open import Coercions using (instᵈ)
open import Conversion using (RevealConversion)
open import ConversionIndexCompatibility using
  (_[_↦_]ᴿ_; _[_↦_⊑⟨_⟩_↤_]ᴾ_)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_,_; proj₂)
open import Data.Sum using (inj₁; inj₂)

open import ImprecisionComposition using
  ( ImprecisionShape
  ; ⌊_⌋
  ; _；_≋_
  )
open import ImprecisionWf using
  ( ImpCtx
  ; _ˣ⊑ˣ_
  ; _∣_⊢_⊑_⊣_
  ; ∀ⁱ_
  ; ⇑ᵢ
  ; ⇑ᴿᵢ
  )
open import NarrowWiden using (_∣_∣_⊢_∶_⊑_)
open import NuReduction using
  ( bind
  ; blame-ν
  ; _—→[_]_
  ; ν-step
  ; ↠-refl
  ; ↠-step
  )
open import NuStore using (StoreWf)
open import NuTermImprecision using
  ( LiftRightStoreⁱ
  ; StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using
  ( RuntimeOK
  ; Term
  ; no•-ν
  ; ok-no
  ; ok-ν
  ; ν
  )
open import PairedWideningCompatibility using
  (PairedWideningCompatible)
open import QuotientedTermImprecision using
  ( prefix-reflⁱ
  ; prefix-∷ⁱ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using (CastMode; SealModeStore★)
open import Types using
  ( Ty
  ; TyCtx
  ; WfTy
  ; ★
  ; `∀
  ; ⇑ᵗ
  ; ⟰ᵗ
  )
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using
  (∀ᵢᶜ; ⊑-lift∀ᵢ; ⊑-target-lift-rightᵢ)
open import proof.Core.Properties.ReductionProperties using (ν-↠; ↠-trans)
open import proof.Core.Properties.NuCastImprecisionShapeProperties using
  (imprecision-composition-shape-transport; shape-target-lift-rightᵢ)
open import proof.Catchup.Simulation.NuImprecisionSimulationCore using
  (weak-one-step-index-resultᵀ)
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  ( WeakOneStepIndexedResult
  ; left-catchup-invariant
  ; left-indexed-all-catchup
  ; left-indexed-catchup
  ; left-silent-invariant
  ; resultStore
  ; sourceCatchup
  ; weakIndexedResult
  )
open import proof.NuCore.Misc.NuImprecisionAllocationSimulation using
  (weak-one-step-matched-ν↑-indexed-value-catchupᵀ)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using (AssumptionMembershipUnique)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessProof
  using
  ( assumption-membership-unique-matched
  ; assumption-membership-unique-⇑ᴿᵢ
  )
open import
  proof.NuCore.Relations.NuImprecisionContextExclusivityDef
  using (SourceNameExclusive)
open import
  proof.NuCore.Relations.NuImprecisionContextExclusivityProof
  using
  ( source-name-exclusive-matched-head
  ; source-name-exclusive-⇑ᴿᵢ
  )
open import
  proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef
  using
  ( WeakOneStepStoreLineage
  ; lineageEmbedding
  ; lineagePrefix
  ; lineageStore
  ; weak-step-store-lineage
  )
open import
  proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageProof
  using (weak-one-step-prepend-left-silent-store-lineageᵀ)
open import proof.Store.Core.NuImprecisionStoreLift using
  (lift-store-result)
open import proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingAlgebra
  using (lift-right-store-embeddingⁱ; lift-store-embeddingⁱ)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef
  using (WorldCoherent)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherenceLemma
  using
  ( world-coherent-matched-allocation
  ; world-coherent-right-allocation
  )
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using
  ( WorldCoherentWeakOneStepIndexedOutcome
  ; world-coherent-left-indexed-catchup
  ; world-indexed-outcome-related
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
  WorldCoherentLeftValueCatchupᵀ →
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {A A′ B B′ C C′ : Ty} {N V′ N′ : Term}
    {s s′} {μ μ′}
    {q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {A⇑⊑A′⇑ : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ ⇑ᵗ A ⊑ ⇑ᵗ A′ ⊣ suc Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  RuntimeOK (ν A N s) →
  RuntimeOK (ν A′ V′ s′) →
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
  ν A′ V′ s′ —→[ bind A′ ] N′ →
  WorldCoherentWeakOneStepIndexedOutcome
    {M = ν A N s} {N′ = N′}
    {χ = bind A′} {ρ = ρ} pB
matched-nu-allocation
    catchup {pA = pA} {A⇑⊑A′⇑ = A⇑⊑A′⇑} {pB = pB}
    coherent exclusive unique wfL wfR ok-source ok-target hA hA′
    s↑ s′↑ N⊑V′ replace (ν-step vV′ noV′)
    with catchup coherent exclusive unique wfL
      (ν-runtime ok-source) vV′ noV′ N⊑V′
matched-nu-allocation
    catchup {pA = pA} {A⇑⊑A′⇑ = A⇑⊑A′⇑} {pB = pB}
    coherent exclusive unique wfL wfR ok-source ok-target hA hA′
    s↑ s′↑ N⊑V′ replace (ν-step vV′ noV′)
    | world-coherent-left-indexed-catchup
        (left-indexed-catchup indexed
          (left-catchup-invariant
            (left-silent-invariant refl refl) final))
        caught-lineage final-coherent final-exclusive final-unique
        final-wfL
    with final
matched-nu-allocation
    catchup {pA = pA} {A⇑⊑A′⇑ = A⇑⊑A′⇑} {pB = pB}
    coherent exclusive unique wfL wfR ok-source ok-target hA hA′
    s↑ s′↑ N⊑V′ replace (ν-step vV′ noV′)
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
    catchup {pA = pA} {A⇑⊑A′⇑ = A⇑⊑A′⇑} {pB = pB}
    coherent exclusive unique wfL wfR ok-source ok-target hA hA′
    s↑ s′↑ N⊑V′ replace (ν-step vV′ noV′)
    | world-coherent-left-indexed-catchup
        (left-indexed-catchup indexed
          (left-catchup-invariant
            (left-silent-invariant refl refl) final))
        caught-lineage final-coherent final-exclusive final-unique
        final-wfL
    | inj₁ (vW , noW)
    =
  world-indexed-outcome-related
    final-indexed
    combined-lineage
    (world-coherent-matched-allocation liftρ⁺ final-coherent)
    (source-name-exclusive-matched-head final-exclusive)
    (assumption-membership-unique-matched final-unique)
  where
  caught-all =
    left-indexed-all-catchup indexed
      (left-catchup-invariant
        (left-silent-invariant refl refl) (inj₁ (vW , noW)))

  final-indexed =
    weak-one-step-matched-ν↑-indexed-value-catchupᵀ
      s↑ s′↑ pA A⇑⊑A′⇑ pB replace vV′ noV′
      caught-all vW noW

  liftρ⁺ = proj₂ (lift-store-result
    (resultStore (weakIndexedResult indexed)))

  combined-lineage : WeakOneStepStoreLineage
    (weakIndexedResult final-indexed)
  combined-lineage =
    weak-one-step-prepend-left-silent-store-lineageᵀ
      _ _
      (weak-step-store-lineage
        (lineageStore caught-lineage)
        (lineageEmbedding caught-lineage)
        (lineagePrefix caught-lineage))
      (weak-step-store-lineage _
        (lift-store-embeddingⁱ liftρ⁺)
        (prefix-∷ⁱ prefix-reflⁱ))


world-coherent-right-one-step-target-allocation-roots-proofᵀ :
  WorldCoherentLeftValueCatchupᵀ →
  WorldCoherentRightOneStepTargetAllocationRoots
world-coherent-right-one-step-target-allocation-roots-proofᵀ catchup =
  record
    { rightStepMatchedNuAllocationRoot =
        matched-nu-allocation catchup
    }

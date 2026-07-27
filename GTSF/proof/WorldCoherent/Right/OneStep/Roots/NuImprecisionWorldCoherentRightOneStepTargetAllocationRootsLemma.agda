module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepTargetAllocationRootsLemma
  where

-- File Charter:
--   * Exposes the matched reveal-ν target-allocation root parameterized by
--     world-coherent left-value catch-up.
--   * Supplies the canonical matched-allocation result and lineage operations
--     at the implementation boundary.
--   * Contains no recursion, postulate, hole, permissive option, dispatcher,
--     or `blame-ν` root.

open import Agda.Builtin.Equality using (refl)
open import Data.Product using (proj₂)

open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepTargetAllocationRootsDef
  using (WorldCoherentRightOneStepTargetAllocationRoots)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepTargetAllocationRootsProof
  using (world-coherent-right-one-step-target-allocation-roots-proofᵀ)
open import
  proof.WorldCoherent.Value.NuImprecisionWorldCoherentValueCatchupDef
  using (WorldCoherentLeftValueCatchupᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Allocation.NuImprecisionWorldCoherentMatchedNuAllocationAfterValueCatchupDef
  using (WorldCoherentMatchedNuAllocationAfterValueCatchupᵀ)
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  ( left-catchup-invariant
  ; left-indexed-all-catchup
  ; left-silent-invariant
  ; resultStore
  ; weakIndexedResult
  )
open import proof.NuCore.Misc.NuImprecisionAllocationSimulation using
  ( weak-one-step-matched-ν↑-indexed-value-catchupᵀ
  ; weak-one-step-matched-ν↑-indexed-value-catchup-lineageᵀ
  )
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessProof
  using (assumption-membership-unique-matched)
open import
  proof.NuCore.Relations.NuImprecisionContextExclusivityProof
  using (source-name-exclusive-matched-head)
open import proof.Store.Core.NuImprecisionStoreLift using
  (lift-store-result)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherenceLemma
  using (world-coherent-matched-allocation)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using (world-indexed-outcome-related)


world-coherent-matched-nu-allocation-after-value-catchupᵀ :
  WorldCoherentMatchedNuAllocationAfterValueCatchupᵀ
world-coherent-matched-nu-allocation-after-value-catchupᵀ
    s↑ s′↑ pA A⇑⊑A′⇑ pB replace vV′ noV′
    catchup@(left-indexed-all-catchup indexed
      (left-catchup-invariant
        (left-silent-invariant refl refl) final))
    vW noW caught-lineage final-coherent final-exclusive final-unique =
  world-indexed-outcome-related
    final-indexed
    combined-lineage
    (world-coherent-matched-allocation liftρ⁺ final-coherent)
    (source-name-exclusive-matched-head final-exclusive)
    (assumption-membership-unique-matched final-unique)
  where
  final-indexed =
    weak-one-step-matched-ν↑-indexed-value-catchupᵀ
      s↑ s′↑ pA A⇑⊑A′⇑ pB replace vV′ noV′
      catchup vW noW

  liftρ⁺ = proj₂ (lift-store-result
    (resultStore (weakIndexedResult indexed)))

  combined-lineage =
    weak-one-step-matched-ν↑-indexed-value-catchup-lineageᵀ
      s↑ s′↑ pA A⇑⊑A′⇑ pB replace vV′ noV′
      catchup vW noW caught-lineage


world-coherent-right-one-step-target-allocation-rootsᵀ :
  WorldCoherentLeftValueCatchupᵀ →
  WorldCoherentRightOneStepTargetAllocationRoots
world-coherent-right-one-step-target-allocation-rootsᵀ =
  world-coherent-right-one-step-target-allocation-roots-proofᵀ
    world-coherent-matched-nu-allocation-after-value-catchupᵀ

module
  proof.WorldCoherent.Right.Target.Terminalization.NuImprecisionWorldCoherentRightTargetPendingNuAllocationAccProof
  where

-- File Charter:
--   * Dispatches the general pending target-`ν` allocation boundary to the
--     four exact incoming/final precision-index cells.
--   * Preserves explicit `∀ⁱ` versus source-only `ν` constructor provenance
--     and performs no target allocation itself.
--   * Contains no result/view/outcome type, postulate, hole, permissive
--     option, termination bypass, catch-all, or broad DGG import.

open import ImprecisionWf using (∀ⁱ_; ν)
open import
  proof.WorldCoherent.Right.Target.Terminalization.NuImprecisionWorldCoherentRightTargetPendingNuAllocationAccDef
  using (WorldCoherentRightTargetPendingNuAllocationAccᵀ)
open import
  proof.WorldCoherent.Right.Target.Terminalization.NuImprecisionWorldCoherentRightTargetPendingNuAllocationAccCellsDef
  using
  ( WorldCoherentRightTargetPendingNuAllocationPairedFromPairedAccᵀ
  ; WorldCoherentRightTargetPendingNuAllocationPairedFromSourceOnlyAccᵀ
  ; WorldCoherentRightTargetPendingNuAllocationSourceOnlyFromPairedAccᵀ
  ; WorldCoherentRightTargetPendingNuAllocationSourceOnlyFromSourceOnlyAccᵀ
  )


world-coherent-right-target-pending-nu-allocation-acc-proofᵀ :
  WorldCoherentRightTargetPendingNuAllocationPairedFromPairedAccᵀ →
  WorldCoherentRightTargetPendingNuAllocationPairedFromSourceOnlyAccᵀ →
  WorldCoherentRightTargetPendingNuAllocationSourceOnlyFromPairedAccᵀ →
  WorldCoherentRightTargetPendingNuAllocationSourceOnlyFromSourceOnlyAccᵀ →
  WorldCoherentRightTargetPendingNuAllocationAccᵀ
world-coherent-right-target-pending-nu-allocation-acc-proofᵀ
    paired-from-paired paired-from-source-only
    source-only-from-paired source-only-from-source-only
    {p = ∀ⁱ p} {r = ∀ⁱ r}
    vW access mode seal★ widening tail coherent
    exclusive unique wfR runtime vV noV noW relation =
  paired-from-paired vW access mode seal★ widening tail coherent
    exclusive unique wfR runtime vV noV noW relation
world-coherent-right-target-pending-nu-allocation-acc-proofᵀ
    paired-from-paired paired-from-source-only
    source-only-from-paired source-only-from-source-only
    {p = ν safeₚ occₚ p} {r = ∀ⁱ r}
    vW access mode seal★ widening tail coherent
    exclusive unique wfR runtime vV noV noW relation =
  paired-from-source-only vW access mode seal★ widening tail coherent
    exclusive unique wfR runtime vV noV noW relation
world-coherent-right-target-pending-nu-allocation-acc-proofᵀ
    paired-from-paired paired-from-source-only
    source-only-from-paired source-only-from-source-only
    {p = ∀ⁱ p} {r = ν safeᵣ occᵣ r}
    vW access mode seal★ widening tail coherent
    exclusive unique wfR runtime vV noV noW relation =
  source-only-from-paired vW access mode seal★ widening tail coherent
    exclusive unique wfR runtime vV noV noW relation
world-coherent-right-target-pending-nu-allocation-acc-proofᵀ
    paired-from-paired paired-from-source-only
    source-only-from-paired source-only-from-source-only
    {p = ν safeₚ occₚ p} {r = ν safeᵣ occᵣ r}
    vW access mode seal★ widening tail coherent
    exclusive unique wfR runtime vV noV noW relation =
  source-only-from-source-only vW access mode seal★ widening tail coherent
    exclusive unique wfR runtime vV noV noW relation

module
  proof.WorldCoherent.Right.Target.Resume.NuImprecisionWorldCoherentRightTargetPendingAllocationContinuationContextLemma
  where

-- File Charter:
--   * Exposes canonical source-silent continuation from a raw paired-lambda
--     pending-allocation prefix into its recursive right-value catch-up.
--   * Keeps arbitrary pending targets outside the value-only generic silent
--     continuation boundary.
--   * Contains no additional theorem shape, result/view/outcome type,
--     postulate, hole, permissive option, or broad DGG import.

open import
  proof.WorldCoherent.Right.Target.Resume.NuImprecisionWorldCoherentRightTargetPendingAllocationContinuationContextDef
  using
  (WorldCoherentRightTargetPendingAllocationContinuationContextᵀ)
open import
  proof.WorldCoherent.Right.Target.Resume.NuImprecisionWorldCoherentRightTargetPendingAllocationContinuationContextProof
  using
  (world-coherent-right-target-pending-allocation-continuation-context-proofᵀ)


world-coherent-right-target-pending-allocation-continuation-contextᵀ :
  WorldCoherentRightTargetPendingAllocationContinuationContextᵀ
world-coherent-right-target-pending-allocation-continuation-contextᵀ
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {ρ = ρ}
    {W = W} {W′ = W′} {D = D} {F = F}
    {s = s} {cs = cs} {t = t}
    first-indexed source-empty source-same target-exact
    first-lineage first-bullet first-context first-prefix
    continued second-context second-prefix =
  world-coherent-right-target-pending-allocation-continuation-context-proofᵀ
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {ρ = ρ}
    {W = W} {W′ = W′} {D = D} {F = F}
    {s = s} {cs = cs} {t = t}
    first-indexed source-empty source-same target-exact
    first-lineage first-bullet first-context first-prefix
    continued second-context second-prefix

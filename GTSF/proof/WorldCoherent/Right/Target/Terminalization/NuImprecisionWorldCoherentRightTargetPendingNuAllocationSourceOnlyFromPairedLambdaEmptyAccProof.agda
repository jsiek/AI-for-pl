module
  proof.WorldCoherent.Right.Target.Terminalization.NuImprecisionWorldCoherentRightTargetPendingNuAllocationSourceOnlyFromPairedLambdaEmptyAccProof
  where

-- File Charter:
--   * Proves the ranked direct paired-lambda inert empty-tail target-`ν`
--     allocation cell from the exact contextual allocation theorem.
--   * Uses the reflexive store prefix and preserves the matched lift/body
--     witnesses exposed by the incoming `Λ⊑Λᵀ` relation.
--   * Does not claim arbitrary pending-tail, relation-shape, or active-cast
--     coverage.
--   * Contains no result/view/outcome type, postulate, hole, permissive
--     option, termination bypass, catch-all, or broad DGG import.

open import QuotientedTermImprecision using (prefix-reflⁱ)
open import
  proof.WorldCoherent.Right.Target.Terminalization.NuImprecisionWorldCoherentRightTargetPendingNuAllocationAccCellsDef
  using
  (WorldCoherentRightTargetPendingNuAllocationSourceOnlyFromPairedLambdaEmptyAccᵀ)
open import
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetWidenInstantiationPairedLambdaAllocationContextDef
  using
  (WorldCoherentRightTargetWidenInstantiationPairedLambdaAllocationContextᵀ)


world-coherent-right-target-pending-nu-allocation-source-only-from-paired-lambda-empty-acc-proofᵀ :
  WorldCoherentRightTargetWidenInstantiationPairedLambdaAllocationContextᵀ →
  WorldCoherentRightTargetPendingNuAllocationSourceOnlyFromPairedLambdaEmptyAccᵀ
world-coherent-right-target-pending-nu-allocation-source-only-from-paired-lambda-empty-acc-proofᵀ
    allocation vW′ access mode seal★ cast inert
    coherent exclusive unique wfR runtime
    vW noW noW′ liftρ liftγ body =
  allocation prefix-reflⁱ coherent exclusive unique wfR runtime
    vW noW vW′ noW′ mode seal★ cast inert liftρ liftγ body

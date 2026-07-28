module
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetWidenInstantiationPairedLambdaPostBetaContextProof
  where

-- File Charter:
--   * Constructs the exact post-allocation paired-lambda target-instantiation
--     relation with `target-instantiationᵀ`.
--   * Supplies the canonical closed endpoints, final values, and final
--     no-bullet evidence while preserving the retained store, cast,
--     body relation, arbitrary universal root, and endpoint-typing
--     provenance.
--   * Contains no catch-up implementation, recursive dispatcher,
--     result/view/outcome type, postulate, hole, permissive option,
--     termination bypass, or broad DGG import.

open import QuotientedTermImprecision using (target-instantiationᵀ)
open import
  proof.Quotient.NuImprecisionTargetInstantiationCreationDef
  using (exact-creationᴱ)
open import
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetWidenInstantiationPairedLambdaPostBetaContextDef
  using
  (WorldCoherentRightTargetWidenInstantiationPairedLambdaPostBetaContextᵀ)


world-coherent-right-target-widen-instantiation-paired-lambda-post-beta-context-proofᵀ :
  WorldCoherentRightTargetWidenInstantiationPairedLambdaPostBetaContextᵀ
world-coherent-right-target-widen-instantiation-paired-lambda-post-beta-context-proofᵀ
    creation =
  target-instantiationᵀ (exact-creationᴱ creation)

module
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetWidenInstantiationPairedLambdaRootContextProof
  where

-- File Charter:
--   * Proves the direct paired-`Λ` target-instantiation leaf from the exact
--     fused target-allocation semantic dependency.
--   * Derives runtime validity for the post-`β-inst` target and prepends the
--     single target keep step contextually.
--   * Contains no opaque inner catch-up premise, recursive dispatcher,
--     result/view/outcome type, postulate, hole, permissive option,
--     termination bypass, or broad DGG import.

open import Data.Product using (_,_)
open import NuReduction using (pure-step; β-inst)
open import NuTerms using
  ( no•-Λ
  ; ok-no
  ; ok-ν
  ; Λ_
  )
open import
  proof.WorldCoherent.Right.Target.Framing.NuImprecisionWorldCoherentRightTargetKeepPrependContextDef
  using (WorldCoherentRightTargetKeepPrependContextᵀ)
open import
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetWidenInstantiationPairedLambdaAllocationContextDef
  using
  (WorldCoherentRightTargetWidenInstantiationPairedLambdaAllocationContextᵀ)
open import
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetWidenInstantiationPairedLambdaRootContextDef
  using
  (WorldCoherentRightTargetWidenInstantiationPairedLambdaRootContextᵀ)


world-coherent-right-target-widen-instantiation-paired-lambda-root-context-proofᵀ :
  WorldCoherentRightTargetWidenInstantiationPairedLambdaAllocationContextᵀ →
  WorldCoherentRightTargetKeepPrependContextᵀ →
  WorldCoherentRightTargetWidenInstantiationPairedLambdaRootContextᵀ
world-coherent-right-target-widen-instantiation-paired-lambda-root-context-proofᵀ
    allocation prepend prefix coherent exclusive unique wfR
    vW noW vW′ noW′ mode seal★ cast inert liftρ liftγ body
    with allocation prefix coherent exclusive unique wfR
      (ok-ν (ok-no (no•-Λ noW′)))
      vW noW vW′ noW′ mode seal★ cast inert liftρ liftγ body
world-coherent-right-target-widen-instantiation-paired-lambda-root-context-proofᵀ
    allocation prepend prefix coherent exclusive unique wfR
    vW noW vW′ noW′ mode seal★ cast inert liftρ liftγ body
    | caught , context-eq , right-prefix =
  prepend
    (pure-step (β-inst (Λ vW′)))
    caught context-eq right-prefix

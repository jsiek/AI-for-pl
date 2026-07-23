module proof.Right.Target.NuImprecisionRightTargetWidenInstPostBetaMatrixProof where

-- File Charter:
--   * Proves the complete post-`β-inst` matrix dispatch by exhaustive
--     inversion of the incoming and final universal precision indices.
--   * Leaves the four semantic cells as explicit higher-order dependencies.
--   * Contains no semantic cell implementation, result/view/outcome type,
--     postulate, hole, permissive option, or termination bypass.

open import ImprecisionWf using (∀ⁱ_; ν)
open import proof.Right.Target.NuImprecisionRightTargetWidenInstPostBetaDef using
  (WorldCoherentRightTargetWidenInstPostBetaᵀ)
open import
  proof.Right.Target.NuImprecisionRightTargetWidenInstPostBetaMatrixDef
  using
  ( WorldCoherentRightTargetWidenInstPostBetaPairedFromPairedᵀ
  ; WorldCoherentRightTargetWidenInstPostBetaPairedFromSourceOnlyᵀ
  ; WorldCoherentRightTargetWidenInstPostBetaPairedᵀ
  ; WorldCoherentRightTargetWidenInstPostBetaSourceOnlyFromPairedᵀ
  ; WorldCoherentRightTargetWidenInstPostBetaSourceOnlyFromSourceOnlyᵀ
  ; WorldCoherentRightTargetWidenInstPostBetaSourceOnlyᵀ
  )


world-coherent-right-target-widen-inst-post-beta-source-only-proofᵀ :
  WorldCoherentRightTargetWidenInstPostBetaSourceOnlyFromPairedᵀ →
  WorldCoherentRightTargetWidenInstPostBetaSourceOnlyFromSourceOnlyᵀ →
  WorldCoherentRightTargetWidenInstPostBetaSourceOnlyᵀ
world-coherent-right-target-widen-inst-post-beta-source-only-proofᵀ
    from-paired from-source-only {p = ∀ⁱ r}
    coherent exclusive unique wfR runtime vV noV vV′ noV′
    mode seal★ body relation =
  from-paired coherent exclusive unique wfR runtime vV noV vV′ noV′
    mode seal★ body relation
world-coherent-right-target-widen-inst-post-beta-source-only-proofᵀ
    from-paired from-source-only {p = ν safeₚ occₚ r}
    coherent exclusive unique wfR runtime vV noV vV′ noV′
    mode seal★ body relation =
  from-source-only coherent exclusive unique wfR runtime vV noV vV′ noV′
    mode seal★ body relation


world-coherent-right-target-widen-inst-post-beta-paired-proofᵀ :
  WorldCoherentRightTargetWidenInstPostBetaPairedFromPairedᵀ →
  WorldCoherentRightTargetWidenInstPostBetaPairedFromSourceOnlyᵀ →
  WorldCoherentRightTargetWidenInstPostBetaPairedᵀ
world-coherent-right-target-widen-inst-post-beta-paired-proofᵀ
    from-paired from-source-only {p = ∀ⁱ r}
    coherent exclusive unique wfR runtime vV noV vV′ noV′
    mode seal★ body relation =
  from-paired coherent exclusive unique wfR runtime vV noV vV′ noV′
    mode seal★ body relation
world-coherent-right-target-widen-inst-post-beta-paired-proofᵀ
    from-paired from-source-only {p = ν safe occ r}
    coherent exclusive unique wfR runtime vV noV vV′ noV′
    mode seal★ body relation =
  from-source-only coherent exclusive unique wfR runtime vV noV vV′ noV′
    mode seal★ body relation


world-coherent-right-target-widen-inst-post-beta-matrix-proofᵀ :
  WorldCoherentRightTargetWidenInstPostBetaSourceOnlyᵀ →
  WorldCoherentRightTargetWidenInstPostBetaPairedᵀ →
  WorldCoherentRightTargetWidenInstPostBetaᵀ
world-coherent-right-target-widen-inst-post-beta-matrix-proofᵀ
    source-only paired {q = ∀ⁱ q}
    coherent exclusive unique wfR runtime vV noV vV′ noV′
    mode seal★ body relation =
  paired coherent exclusive unique wfR runtime vV noV vV′ noV′
    mode seal★ body relation
world-coherent-right-target-widen-inst-post-beta-matrix-proofᵀ
    source-only paired {q = ν safe occ q}
    coherent exclusive unique wfR runtime vV noV vV′ noV′
    mode seal★ body relation =
  source-only {{safe}} coherent exclusive unique wfR runtime
    vV noV vV′ noV′ mode seal★ body relation

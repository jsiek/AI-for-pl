module
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetWidenInstantiationRootProof
  where

-- File Charter:
--   * Dispatches the general target-instantiation root to the paired or
--     source-only final universal index.
--   * Proves the complete index matrix while leaving the four semantic cells
--     as explicit higher-order dependencies.
--   * Contains no implementation of a cell, result/view/outcome type,
--     postulate, hole, permissive option, or termination bypass.

open import ImprecisionWf using (∀ⁱ_; ν)
open import
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetWidenInstantiationRootDef
  using
  ( WorldCoherentRightTargetWidenInstantiationPairedFromPairedRootᵀ
  ; WorldCoherentRightTargetWidenInstantiationPairedFromSourceOnlyRootᵀ
  ; WorldCoherentRightTargetWidenInstantiationPairedRootᵀ
  ; WorldCoherentRightTargetWidenInstantiationRootᵀ
  ; WorldCoherentRightTargetWidenInstantiationSourceOnlyFromPairedRootᵀ
  ; WorldCoherentRightTargetWidenInstantiationSourceOnlyFromSourceOnlyRootᵀ
  ; WorldCoherentRightTargetWidenInstantiationSourceOnlyRootᵀ
  )


world-coherent-right-target-widen-instantiation-source-only-root-proofᵀ :
  WorldCoherentRightTargetWidenInstantiationSourceOnlyFromPairedRootᵀ →
  WorldCoherentRightTargetWidenInstantiationSourceOnlyFromSourceOnlyRootᵀ →
  WorldCoherentRightTargetWidenInstantiationSourceOnlyRootᵀ
world-coherent-right-target-widen-instantiation-source-only-root-proofᵀ
    from-paired from-source-only {p = ∀ⁱ r}
    allocation prefix coherent exclusive unique wfR runtime
    vV noV mode seal★ c⊑ relation caught =
  from-paired allocation prefix coherent exclusive unique wfR
    runtime vV noV mode seal★ c⊑ relation caught
world-coherent-right-target-widen-instantiation-source-only-root-proofᵀ
    from-paired from-source-only {p = ν safeₚ occₚ r}
    allocation prefix coherent exclusive unique wfR runtime
    vV noV mode seal★ c⊑ relation caught =
  from-source-only allocation prefix coherent exclusive unique wfR
    runtime vV noV mode seal★ c⊑ relation caught


world-coherent-right-target-widen-instantiation-paired-root-proofᵀ :
  WorldCoherentRightTargetWidenInstantiationPairedFromPairedRootᵀ →
  WorldCoherentRightTargetWidenInstantiationPairedFromSourceOnlyRootᵀ →
  WorldCoherentRightTargetWidenInstantiationPairedRootᵀ
world-coherent-right-target-widen-instantiation-paired-root-proofᵀ
    from-paired from-source-only {p = ∀ⁱ r}
    allocation prefix coherent exclusive unique wfR runtime
    vV noV mode seal★ c⊑ relation caught =
  from-paired allocation prefix coherent exclusive unique wfR
    runtime vV noV mode seal★ c⊑ relation caught
world-coherent-right-target-widen-instantiation-paired-root-proofᵀ
    from-paired from-source-only {p = ν safe occ r}
    allocation prefix coherent exclusive unique wfR runtime
    vV noV mode seal★ c⊑ relation caught =
  from-source-only allocation prefix coherent exclusive unique wfR
    runtime vV noV mode seal★ c⊑ relation caught


world-coherent-right-target-widen-instantiation-root-proofᵀ :
  WorldCoherentRightTargetWidenInstantiationSourceOnlyRootᵀ →
  WorldCoherentRightTargetWidenInstantiationPairedRootᵀ →
  WorldCoherentRightTargetWidenInstantiationRootᵀ
world-coherent-right-target-widen-instantiation-root-proofᵀ
    source-only paired {q = ∀ⁱ q}
    allocation prefix coherent exclusive unique wfR runtime
    vV noV mode seal★ c⊑ relation caught =
  paired allocation prefix coherent exclusive unique wfR runtime
    vV noV mode seal★ c⊑ relation caught
world-coherent-right-target-widen-instantiation-root-proofᵀ
    source-only paired {q = ν safe occ q}
    allocation prefix coherent exclusive unique wfR runtime
    vV noV mode seal★ c⊑ relation caught =
  source-only {{safe}} allocation prefix coherent exclusive unique
    wfR runtime vV noV mode seal★ c⊑ relation caught

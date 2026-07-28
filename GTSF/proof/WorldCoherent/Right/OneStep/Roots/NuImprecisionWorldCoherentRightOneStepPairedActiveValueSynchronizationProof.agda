module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPairedActiveValueSynchronizationProof
  where

-- File Charter:
--   * Restricts the exact live paired source-active value-root cells to final
--     source values.
--   * Reuses reveal, conceal, and widening constructor evidence directly;
--     endpoint syntax is never used as an inversion principle.
--   * Contains no target-root dispatch, generic paired-cast abstraction,
--     quotient case, recursion, postulate, hole, or permissive option.

open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPairedActiveValueSynchronizationDef
  using (WorldCoherentRightOneStepPairedActiveValueSynchronizationᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPairedSourceActiveValueRootDef
  using
  ( WorldCoherentRightOneStepPairedSourceActiveValueRootᵀ
  ; active-paired-conceal-root
  ; active-paired-reveal-root
  ; active-paired-widening-root
  )


world-coherent-right-one-step-paired-active-value-synchronization-proofᵀ :
  WorldCoherentRightOneStepPairedSourceActiveValueRootᵀ →
  WorldCoherentRightOneStepPairedActiveValueSynchronizationᵀ
world-coherent-right-one-step-paired-active-value-synchronization-proofᵀ
    active-root =
  record
    { synchronize-paired-reveal =
        λ coherent exclusive unique wfL wfR
          ok-source ok-target vV noV vV′ noV′ noninert
          corr c↑ c′↑ replacement V⊑V′ target-root →
        active-paired-reveal-root active-root
          coherent exclusive unique wfL wfR
          ok-source ok-target vV′ noninert
          corr c↑ c′↑ replacement V⊑V′ target-root
    ; synchronize-paired-conceal =
        λ coherent exclusive unique wfL wfR
          ok-source ok-target vV noV vV′ noV′ noninert
          corr c↓ c′↓ replacement V⊑V′ target-root →
        active-paired-conceal-root active-root
          coherent exclusive unique wfL wfR
          ok-source ok-target vV′ noninert
          corr c↓ c′↓ replacement V⊑V′ target-root
    ; synchronize-paired-widening =
        λ coherent exclusive unique wfL wfR
          ok-source ok-target vV noV vV′ noV′ noninert
          mode seal★ c⊑ c-shape mode′ seal★′ c′⊑ c′-shape
          source-comp target-comp compatible V⊑V′ target-root →
        active-paired-widening-root active-root
          coherent exclusive unique wfL wfR
          ok-source ok-target vV′ noninert
          mode seal★ c⊑ c-shape mode′ seal★′ c′⊑ c′-shape
          source-comp target-comp compatible V⊑V′ target-root
    }

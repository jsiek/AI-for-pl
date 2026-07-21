module
  proof.NuImprecisionWorldCoherentSourceNuPairedLambdaTargetClosingCatchupProof
  where

-- File Charter:
--   * Removes the administrative post-allocation `β-Λ•` step from direct
--     paired source-`ν` target-binder closing.
--   * Delegates semantic target-closing reveal catch-up and shared keep-step
--     prepending to focused theorem dependencies.
--   * Contains no recursive dispatcher, postulate, or permissive option.

open import
  proof.NuImprecisionWorldCoherentLeftCatchupPrependKeepStep using
  ( post-allocation-β-Λ-cast
  ; world-coherent-left-catchup-prepend-keep-step
  )
open import
  proof.NuImprecisionWorldCoherentPairedLambdaTargetClosingRevealCatchupDef
  using (WorldCoherentPairedLambdaTargetClosingRevealCatchupᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceNuPairedLambdaTargetClosingCatchupDef
  using (WorldCoherentSourceNuPairedLambdaTargetClosingCatchupᵀ)


world-coherent-source-ν-paired-lambda-target-closing-catchup-proofᵀ :
  WorldCoherentPairedLambdaTargetClosingRevealCatchupᵀ →
  WorldCoherentSourceNuPairedLambdaTargetClosingCatchupᵀ
world-coherent-source-ν-paired-lambda-target-closing-catchup-proofᵀ
    closing-reveal coherent exclusive wfL hA h⇑A s↑ liftν lift∀
    vW noW vW′ noW′ W⊑W′ =
  world-coherent-left-catchup-prepend-keep-step
    (post-allocation-β-Λ-cast vW)
    (closing-reveal coherent exclusive wfL hA h⇑A s↑ liftν lift∀
      vW noW vW′ noW′ W⊑W′)

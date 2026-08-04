module
  proof.Right.SourceAll.Bodies.NuImprecisionRightSourceAllCastBodyProof
  where

-- File Charter:
--   * Proves the inert-cast body case of source-universal right-value closing
--     from the flat source-all case capabilities.
--   * Handles target bullet and allocation syntax before QTI inversion, then
--     dispatches all cast, quotient, prefix, and eager-gen constructors.
--   * Contains no recursion, result/view/outcome type, postulate, hole,
--     incomplete match, permissive option, or broad simulation import.

open import NuTerms using
  ( no•-ν
  ; no•-⟨⟩
  ; ok-no
  ; ok-•
  ; ok-ν
  ; Λ_
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  ( cast⊒⊑ᵀ
  ; cast⊑⊑ᵀ
  ; closeᵀ
  ; conv↑⊑ᵀ
  ; conv↓⊑ᵀ
  ; gen⊑groundᵀ
  ; paired-concealᵀ
  ; paired-revealᵀ
  ; paired-wideningᵀ
  ; ⊑cast⊒ᵀ
  ; ⊑cast⊑ᵀ
  ; ⊑conv↑ᵀ
  ; ⊑conv↓ᵀ
  )
open import proof.DGG.Core.NuProgress using (runtime-value-no•)
open import
  proof.Right.SourceAll.Bodies.NuImprecisionRightSourceAllCastBodyDef
  using (WorldCoherentRightSourceAllCastBodyᵀ)
open import
  proof.Right.SourceAll.ClosingValues.NuImprecisionRightSourceAllClosingCasesDef
  using
  ( WorldCoherentRightSourceAllClosingCases
  ; sourceAllResidualCases
  ; sourceAllSourceFramesCase
  ; sourceAllTargetConcealFrameCase
  ; sourceAllTargetNarrowFrameCase
  ; sourceAllTargetRevealFrameCase
  ; sourceAllTargetWidenFrameCase
  ; sourceAllTerminalCase
  )
open import
  proof.Right.SourceAll.Core.NuImprecisionRightSourceAllResidualCasesDef
  using
  ( sourceAllPairedConceal
  ; sourceAllPairedReveal
  ; sourceAllPairedWidening
  ; sourceAllQuotient
  ; sourceAllTargetAllocation
  ; sourceAllTargetBullet
  )
open import
  proof.Right.SourceAll.Frames.NuImprecisionRightSourceAllSourceFramesDef
  using
  ( sourceAllSourceConcealFrame
  ; sourceAllSourceNarrowFrame
  ; sourceAllSourceRevealFrame
  ; sourceAllSourceWidenFrame
  )


world-coherent-right-source-all-cast-body-proofᵀ :
  WorldCoherentRightSourceAllClosingCases →
  WorldCoherentRightSourceAllCastBodyᵀ
world-coherent-right-source-all-cast-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    ok•@(ok-• vV′ noV′) vM noM inert liftρ liftγ rel =
  sourceAllTargetBullet (sourceAllResidualCases cases)
    prefix coherent exclusive unique wfR ok•
    (vM ⟨ inert ⟩) (no•-⟨⟩ noM) liftρ liftγ rel
world-coherent-right-source-all-cast-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    okν@(ok-ν okN′) vM noM inert liftρ liftγ rel =
  sourceAllTargetAllocation (sourceAllResidualCases cases)
    prefix coherent exclusive unique wfR okν
    (vM ⟨ inert ⟩) (no•-⟨⟩ noM) liftρ liftγ rel
world-coherent-right-source-all-cast-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    okν@(ok-no (no•-ν noN′)) vM noM inert liftρ liftγ rel =
  sourceAllTargetAllocation (sourceAllResidualCases cases)
    prefix coherent exclusive unique wfR okν
    (vM ⟨ inert ⟩) (no•-⟨⟩ noM) liftρ liftγ rel
world-coherent-right-source-all-cast-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    ok-up vM noM inert liftρ liftγ
    (closeᵀ paired widening pA
      source-shape target-shape square compatible) =
  sourceAllQuotient (sourceAllResidualCases cases)
    prefix coherent exclusive unique wfR ok-up
    (vM ⟨ inert ⟩) (no•-⟨⟩ noM)
    liftρ liftγ paired widening
    source-shape target-shape square compatible
world-coherent-right-source-all-cast-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    okW vM noM inert liftρ liftγ
    rel@(gen⊑groundᵀ mode seal★ c⊒ gH vV vW
      W⊢ V⊑Wtag q) =
  sourceAllTerminalCase cases prefix coherent exclusive unique wfR
    (vM ⟨ inert ⟩) (no•-⟨⟩ noM)
    vW (runtime-value-no• okW vW) liftρ liftγ rel
world-coherent-right-source-all-cast-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    okN′ vM noM inert liftρ liftγ
    (cast⊒⊑ᵀ mode seal★ c⊒ inner q c-shape comp) =
  sourceAllSourceNarrowFrame (sourceAllSourceFramesCase cases)
    prefix coherent exclusive unique wfR okN′
    vM noM inert mode seal★ c⊒ c-shape comp liftρ liftγ inner
world-coherent-right-source-all-cast-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    okN′ vM noM inert liftρ liftγ
    (cast⊑⊑ᵀ mode seal★ c⊑ inner q c-shape comp) =
  sourceAllSourceWidenFrame (sourceAllSourceFramesCase cases)
    prefix coherent exclusive unique wfR okN′
    vM noM inert mode seal★ c⊑ c-shape comp liftρ liftγ inner
world-coherent-right-source-all-cast-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    ok-cast vM noM inert liftρ liftγ
    (⊑cast⊒ᵀ mode seal★ c⊒ inner q c-shape comp) =
  sourceAllTargetNarrowFrameCase cases
    prefix coherent exclusive unique wfR ok-cast
    (vM ⟨ inert ⟩) (no•-⟨⟩ noM)
    mode seal★ c⊒ c-shape comp liftρ liftγ inner
world-coherent-right-source-all-cast-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    ok-cast vM noM inert liftρ liftγ
    (⊑cast⊑ᵀ mode seal★ c⊑ inner q c-shape comp) =
  sourceAllTargetWidenFrameCase cases
    prefix coherent exclusive unique wfR ok-cast
    (vM ⟨ inert ⟩) (no•-⟨⟩ noM)
    mode seal★ c⊑ c-shape comp liftρ liftγ inner
world-coherent-right-source-all-cast-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    ok-paired vM noM inert liftρ liftγ
    (paired-revealᵀ corr c↑ c′↑ replacement inner) =
  sourceAllPairedReveal (sourceAllResidualCases cases)
    prefix coherent exclusive unique wfR ok-paired
    vM noM inert liftρ liftγ
    corr c↑ c′↑ replacement inner
world-coherent-right-source-all-cast-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    ok-paired vM noM inert liftρ liftγ
    (paired-concealᵀ corr c↓ c′↓ replacement inner) =
  sourceAllPairedConceal (sourceAllResidualCases cases)
    prefix coherent exclusive unique wfR ok-paired
    vM noM inert liftρ liftγ
    corr c↓ c′↓ replacement inner
world-coherent-right-source-all-cast-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    ok-paired vM noM inert liftρ liftγ
    (paired-wideningᵀ
      mode seal★ c⊑ c-shape
      mode′ seal★′ c′⊑ c′-shape
      left-square right-square compatible inner) =
  sourceAllPairedWidening (sourceAllResidualCases cases)
    prefix coherent exclusive unique wfR ok-paired
    vM noM inert liftρ liftγ
    mode seal★ c⊑ c-shape
    mode′ seal★′ c′⊑ c′-shape
    left-square right-square compatible inner
world-coherent-right-source-all-cast-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    okN′ vM noM inert liftρ liftγ
    (conv↑⊑ᵀ c↑ inner q replacement) =
  sourceAllSourceRevealFrame (sourceAllSourceFramesCase cases)
    prefix coherent exclusive unique wfR okN′
    vM noM inert c↑ replacement liftρ liftγ inner
world-coherent-right-source-all-cast-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    okN′ vM noM inert liftρ liftγ
    (conv↓⊑ᵀ c↓ inner q replacement) =
  sourceAllSourceConcealFrame (sourceAllSourceFramesCase cases)
    prefix coherent exclusive unique wfR okN′
    vM noM inert c↓ replacement liftρ liftγ inner
world-coherent-right-source-all-cast-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    ok-cast vM noM inert liftρ liftγ
    (⊑conv↑ᵀ c↑ inner q replacement) =
  sourceAllTargetRevealFrameCase cases
    prefix coherent exclusive unique wfR ok-cast
    (vM ⟨ inert ⟩) (no•-⟨⟩ noM)
    c↑ replacement liftρ liftγ inner
world-coherent-right-source-all-cast-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    ok-cast vM noM inert liftρ liftγ
    (⊑conv↓ᵀ c↓ inner q replacement) =
  sourceAllTargetConcealFrameCase cases
    prefix coherent exclusive unique wfR ok-cast
    (vM ⟨ inert ⟩) (no•-⟨⟩ noM)
    c↓ replacement liftρ liftγ inner

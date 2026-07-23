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
  ( allocation-prefixᵀ
  ; cast⊒⊑ᵀ
  ; cast⊑⊑ᵀ
  ; conv↑⊑ᵀ
  ; conv↓⊑ᵀ
  ; conv⊑convᵀ
  ; gen⊑groundᵀ
  ; up⊑upᵀ
  ; ⊑cast⊒ᵀ
  ; ⊑cast⊑idᵀ
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
  ; sourceAllAllocationPrefixCase
  ; sourceAllResidualCases
  ; sourceAllSourceFramesCase
  ; sourceAllTargetConcealFrameCase
  ; sourceAllTargetIdWidenFrameCase
  ; sourceAllTargetNarrowFrameCase
  ; sourceAllTargetRevealFrameCase
  ; sourceAllTargetWidenFrameCase
  ; sourceAllTerminalCase
  )
open import
  proof.Right.SourceAll.Core.NuImprecisionRightSourceAllResidualCasesDef
  using
  ( sourceAllPairedCast
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
    (up⊑upᵀ paired widening pA) =
  sourceAllQuotient (sourceAllResidualCases cases)
    prefix coherent exclusive unique wfR ok-up
    (vM ⟨ inert ⟩) (no•-⟨⟩ noM)
    liftρ liftγ paired widening
world-coherent-right-source-all-cast-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    okN′ vM noM inert liftρ liftγ
    (allocation-prefixᵀ prefix′ inner V⊢ N′⊢) =
  sourceAllAllocationPrefixCase cases
    prefix coherent exclusive unique wfR okN′
    (vM ⟨ inert ⟩) (no•-⟨⟩ noM)
    liftρ liftγ prefix′ inner
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
    (cast⊒⊑ᵀ mode seal★ c⊒ inner q) =
  sourceAllSourceNarrowFrame (sourceAllSourceFramesCase cases)
    prefix coherent exclusive unique wfR okN′
    vM noM inert mode seal★ c⊒ liftρ liftγ inner
world-coherent-right-source-all-cast-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    okN′ vM noM inert liftρ liftγ
    (cast⊑⊑ᵀ mode seal★ c⊑ inner q) =
  sourceAllSourceWidenFrame (sourceAllSourceFramesCase cases)
    prefix coherent exclusive unique wfR okN′
    vM noM inert mode seal★ c⊑ liftρ liftγ inner
world-coherent-right-source-all-cast-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    ok-cast vM noM inert liftρ liftγ
    (⊑cast⊒ᵀ mode seal★ c⊒ inner q) =
  sourceAllTargetNarrowFrameCase cases
    prefix coherent exclusive unique wfR ok-cast
    (vM ⟨ inert ⟩) (no•-⟨⟩ noM)
    mode seal★ c⊒ liftρ liftγ inner
world-coherent-right-source-all-cast-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    ok-cast vM noM inert liftρ liftγ
    (⊑cast⊑ᵀ mode seal★ c⊑ inner q) =
  sourceAllTargetWidenFrameCase cases
    prefix coherent exclusive unique wfR ok-cast
    (vM ⟨ inert ⟩) (no•-⟨⟩ noM)
    mode seal★ c⊑ liftρ liftγ inner
world-coherent-right-source-all-cast-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    ok-cast vM noM inert liftρ liftγ
    (⊑cast⊑idᵀ seal★ c⊑ inner q) =
  sourceAllTargetIdWidenFrameCase cases
    prefix coherent exclusive unique wfR ok-cast
    (vM ⟨ inert ⟩) (no•-⟨⟩ noM)
    seal★ c⊑ liftρ liftγ inner
world-coherent-right-source-all-cast-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    ok-paired vM noM inert liftρ liftγ
    (conv⊑convᵀ paired inner) =
  sourceAllPairedCast (sourceAllResidualCases cases)
    prefix coherent exclusive unique wfR ok-paired
    vM noM inert liftρ liftγ paired inner
world-coherent-right-source-all-cast-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    okN′ vM noM inert liftρ liftγ
    (conv↑⊑ᵀ c↑ inner q) =
  sourceAllSourceRevealFrame (sourceAllSourceFramesCase cases)
    prefix coherent exclusive unique wfR okN′
    vM noM inert c↑ liftρ liftγ inner
world-coherent-right-source-all-cast-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    okN′ vM noM inert liftρ liftγ
    (conv↓⊑ᵀ c↓ inner q) =
  sourceAllSourceConcealFrame (sourceAllSourceFramesCase cases)
    prefix coherent exclusive unique wfR okN′
    vM noM inert c↓ liftρ liftγ inner
world-coherent-right-source-all-cast-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    ok-cast vM noM inert liftρ liftγ
    (⊑conv↑ᵀ c↑ inner q) =
  sourceAllTargetRevealFrameCase cases
    prefix coherent exclusive unique wfR ok-cast
    (vM ⟨ inert ⟩) (no•-⟨⟩ noM)
    c↑ liftρ liftγ inner
world-coherent-right-source-all-cast-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    ok-cast vM noM inert liftρ liftγ
    (⊑conv↓ᵀ c↓ inner q) =
  sourceAllTargetConcealFrameCase cases
    prefix coherent exclusive unique wfR ok-cast
    (vM ⟨ inert ⟩) (no•-⟨⟩ noM)
    c↓ liftρ liftγ inner

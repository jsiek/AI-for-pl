module
  proof.Right.SourceAll.Bodies.NuImprecisionRightSourceAllLambdaBodyProof
  where

-- File Charter:
--   * Proves the term-lambda body case of source-universal right-value
--     closing from the flat source-all case capabilities.
--   * Splits target runtime syntax before QTI, keeping computed allocation
--     context lifts out of ambiguous constructor inversion.
--   * Contains no recursion, result/view/outcome type, postulate, hole,
--     incomplete match, permissive option, or broad simulation import.

open import NuTerms using
  ( no•-`
  ; no•-$
  ; no•-·
  ; no•-ƛ
  ; no•-Λ
  ; no•-ν
  ; no•-⊕
  ; no•-⟨⟩
  ; no•-blame
  ; ok-no
  ; ok-•
  ; ok-·₁
  ; ok-·₂
  ; ok-ν
  ; ok-⊕₁
  ; ok-⊕₂
  ; ok-⟨⟩
  ; ƛ_
  ; $
  )
open import QuotientedTermImprecision using
  ( ⊑cast⊒ᵀ
  ; ⊑cast⊑ᵀ
  ; ⊑conv↑ᵀ
  ; ⊑conv↓ᵀ
  )
open import
  proof.Right.SourceAll.ClosingValues.NuImprecisionRightSourceAllClosingCasesDef
  using
  ( WorldCoherentRightSourceAllClosingCases
  ; sourceAllResidualCases
  ; sourceAllTargetConcealFrameCase
  ; sourceAllTargetNarrowFrameCase
  ; sourceAllTargetRevealFrameCase
  ; sourceAllTargetWidenFrameCase
  ; sourceAllTerminalCase
  )
open import
  proof.Right.SourceAll.Bodies.NuImprecisionRightSourceAllLambdaBodyDef
  using (WorldCoherentRightSourceAllLambdaBodyᵀ)
open import
  proof.Right.SourceAll.Core.NuImprecisionRightSourceAllResidualCasesDef
  using (sourceAllTargetAllocation; sourceAllTargetBullet)


world-coherent-right-source-all-lambda-body-proofᵀ :
  WorldCoherentRightSourceAllClosingCases →
  WorldCoherentRightSourceAllLambdaBodyᵀ
world-coherent-right-source-all-lambda-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    (ok-no (no•-ƛ noN′)) noN liftρ liftγ rel =
  sourceAllTerminalCase cases prefix coherent exclusive unique wfR
    (ƛ _) (no•-ƛ noN) (ƛ _) (no•-ƛ noN′)
    liftρ liftγ rel
world-coherent-right-source-all-lambda-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    (ok-no no•-$) noN liftρ liftγ rel =
  sourceAllTerminalCase cases prefix coherent exclusive unique wfR
    (ƛ _) (no•-ƛ noN) ($ _) no•-$ liftρ liftγ rel
world-coherent-right-source-all-lambda-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    ok-cast@(ok-no (no•-⟨⟩ noN′)) noN liftρ liftγ
    (⊑cast⊒ᵀ mode seal★ c⊒ inner q c-shape comp) =
  sourceAllTargetNarrowFrameCase cases
    prefix coherent exclusive unique wfR ok-cast
    (ƛ _) (no•-ƛ noN) mode seal★ c⊒ c-shape comp liftρ liftγ inner
world-coherent-right-source-all-lambda-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    ok-cast@(ok-no (no•-⟨⟩ noN′)) noN liftρ liftγ
    (⊑cast⊑ᵀ mode seal★ c⊑ inner q c-shape comp) =
  sourceAllTargetWidenFrameCase cases
    prefix coherent exclusive unique wfR ok-cast
    (ƛ _) (no•-ƛ noN) mode seal★ c⊑ c-shape comp liftρ liftγ inner
world-coherent-right-source-all-lambda-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    ok-cast@(ok-no (no•-⟨⟩ noN′)) noN liftρ liftγ
    (⊑conv↑ᵀ c↑ inner q replacement) =
  sourceAllTargetRevealFrameCase cases
    prefix coherent exclusive unique wfR ok-cast
    (ƛ _) (no•-ƛ noN) c↑ replacement liftρ liftγ inner
world-coherent-right-source-all-lambda-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    ok-cast@(ok-no (no•-⟨⟩ noN′)) noN liftρ liftγ
    (⊑conv↓ᵀ c↓ inner q replacement) =
  sourceAllTargetConcealFrameCase cases
    prefix coherent exclusive unique wfR ok-cast
    (ƛ _) (no•-ƛ noN) c↓ replacement liftρ liftγ inner
world-coherent-right-source-all-lambda-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    okν@(ok-no (no•-ν noN′)) noN liftρ liftγ rel =
  sourceAllTargetAllocation (sourceAllResidualCases cases)
    prefix coherent exclusive unique wfR okν
    (ƛ _) (no•-ƛ noN) liftρ liftγ rel
world-coherent-right-source-all-lambda-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    ok•@(ok-• vV′ noV′) noN liftρ liftγ rel =
  sourceAllTargetBullet (sourceAllResidualCases cases)
    prefix coherent exclusive unique wfR ok•
    (ƛ _) (no•-ƛ noN) liftρ liftγ rel
world-coherent-right-source-all-lambda-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    okν@(ok-ν okN′) noN liftρ liftγ rel =
  sourceAllTargetAllocation (sourceAllResidualCases cases)
    prefix coherent exclusive unique wfR okν
    (ƛ _) (no•-ƛ noN) liftρ liftγ rel
world-coherent-right-source-all-lambda-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    ok-cast@(ok-⟨⟩ okN′) noN liftρ liftγ
    (⊑cast⊒ᵀ mode seal★ c⊒ inner q c-shape comp) =
  sourceAllTargetNarrowFrameCase cases
    prefix coherent exclusive unique wfR ok-cast
    (ƛ _) (no•-ƛ noN) mode seal★ c⊒ c-shape comp liftρ liftγ inner
world-coherent-right-source-all-lambda-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    ok-cast@(ok-⟨⟩ okN′) noN liftρ liftγ
    (⊑cast⊑ᵀ mode seal★ c⊑ inner q c-shape comp) =
  sourceAllTargetWidenFrameCase cases
    prefix coherent exclusive unique wfR ok-cast
    (ƛ _) (no•-ƛ noN) mode seal★ c⊑ c-shape comp liftρ liftγ inner
world-coherent-right-source-all-lambda-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    ok-cast@(ok-⟨⟩ okN′) noN liftρ liftγ
    (⊑conv↑ᵀ c↑ inner q replacement) =
  sourceAllTargetRevealFrameCase cases
    prefix coherent exclusive unique wfR ok-cast
    (ƛ _) (no•-ƛ noN) c↑ replacement liftρ liftγ inner
world-coherent-right-source-all-lambda-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    ok-cast@(ok-⟨⟩ okN′) noN liftρ liftγ
    (⊑conv↓ᵀ c↓ inner q replacement) =
  sourceAllTargetConcealFrameCase cases
    prefix coherent exclusive unique wfR ok-cast
    (ƛ _) (no•-ƛ noN) c↓ replacement liftρ liftγ inner

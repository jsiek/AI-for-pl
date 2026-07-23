module
  proof.NuImprecisionRightSourceAllLambdaBodyProof
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
  ( allocation-prefixᵀ
  ; ⊑cast⊒ᵀ
  ; ⊑cast⊑idᵀ
  ; ⊑cast⊑ᵀ
  ; ⊑conv↑ᵀ
  ; ⊑conv↓ᵀ
  )
open import
  proof.NuImprecisionRightSourceAllClosingCasesDef
  using
  ( WorldCoherentRightSourceAllClosingCases
  ; sourceAllAllocationPrefixCase
  ; sourceAllResidualCases
  ; sourceAllTargetConcealFrameCase
  ; sourceAllTargetIdWidenFrameCase
  ; sourceAllTargetNarrowFrameCase
  ; sourceAllTargetRevealFrameCase
  ; sourceAllTargetWidenFrameCase
  ; sourceAllTerminalCase
  )
open import
  proof.NuImprecisionRightSourceAllLambdaBodyDef
  using (WorldCoherentRightSourceAllLambdaBodyᵀ)
open import
  proof.NuImprecisionRightSourceAllResidualCasesDef
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
    (allocation-prefixᵀ prefix′ inner N⊢ N′⊢) =
  sourceAllAllocationPrefixCase cases
    prefix coherent exclusive unique wfR ok-cast
    (ƛ _) (no•-ƛ noN) liftρ liftγ prefix′ inner
world-coherent-right-source-all-lambda-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    ok-cast@(ok-no (no•-⟨⟩ noN′)) noN liftρ liftγ
    (⊑cast⊒ᵀ mode seal★ c⊒ inner q) =
  sourceAllTargetNarrowFrameCase cases
    prefix coherent exclusive unique wfR ok-cast
    (ƛ _) (no•-ƛ noN) mode seal★ c⊒ liftρ liftγ inner
world-coherent-right-source-all-lambda-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    ok-cast@(ok-no (no•-⟨⟩ noN′)) noN liftρ liftγ
    (⊑cast⊑ᵀ mode seal★ c⊑ inner q) =
  sourceAllTargetWidenFrameCase cases
    prefix coherent exclusive unique wfR ok-cast
    (ƛ _) (no•-ƛ noN) mode seal★ c⊑ liftρ liftγ inner
world-coherent-right-source-all-lambda-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    ok-cast@(ok-no (no•-⟨⟩ noN′)) noN liftρ liftγ
    (⊑cast⊑idᵀ seal★ c⊑ inner q) =
  sourceAllTargetIdWidenFrameCase cases
    prefix coherent exclusive unique wfR ok-cast
    (ƛ _) (no•-ƛ noN) seal★ c⊑ liftρ liftγ inner
world-coherent-right-source-all-lambda-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    ok-cast@(ok-no (no•-⟨⟩ noN′)) noN liftρ liftγ
    (⊑conv↑ᵀ c↑ inner q) =
  sourceAllTargetRevealFrameCase cases
    prefix coherent exclusive unique wfR ok-cast
    (ƛ _) (no•-ƛ noN) c↑ liftρ liftγ inner
world-coherent-right-source-all-lambda-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    ok-cast@(ok-no (no•-⟨⟩ noN′)) noN liftρ liftγ
    (⊑conv↓ᵀ c↓ inner q) =
  sourceAllTargetConcealFrameCase cases
    prefix coherent exclusive unique wfR ok-cast
    (ƛ _) (no•-ƛ noN) c↓ liftρ liftγ inner
world-coherent-right-source-all-lambda-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    okν@(ok-no (no•-ν noN′)) noN liftρ liftγ rel =
  sourceAllTargetAllocation (sourceAllResidualCases cases)
    prefix coherent exclusive unique wfR okν
    (ƛ _) (no•-ƛ noN) liftρ liftγ rel
world-coherent-right-source-all-lambda-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    okVar@(ok-no no•-`) noN liftρ liftγ
    (allocation-prefixᵀ prefix′ inner N⊢ N′⊢) =
  sourceAllAllocationPrefixCase cases
    prefix coherent exclusive unique wfR okVar
    (ƛ _) (no•-ƛ noN) liftρ liftγ prefix′ inner
world-coherent-right-source-all-lambda-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    okApp@(ok-no (no•-· noL′ noM′)) noN liftρ liftγ
    (allocation-prefixᵀ prefix′ inner N⊢ N′⊢) =
  sourceAllAllocationPrefixCase cases
    prefix coherent exclusive unique wfR okApp
    (ƛ _) (no•-ƛ noN) liftρ liftγ prefix′ inner
world-coherent-right-source-all-lambda-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    okΛ@(ok-no (no•-Λ noN′)) noN liftρ liftγ
    (allocation-prefixᵀ prefix′ inner N⊢ N′⊢) =
  sourceAllAllocationPrefixCase cases
    prefix coherent exclusive unique wfR okΛ
    (ƛ _) (no•-ƛ noN) liftρ liftγ prefix′ inner
world-coherent-right-source-all-lambda-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    okPlus@(ok-no (no•-⊕ noL′ noM′)) noN liftρ liftγ
    (allocation-prefixᵀ prefix′ inner N⊢ N′⊢) =
  sourceAllAllocationPrefixCase cases
    prefix coherent exclusive unique wfR okPlus
    (ƛ _) (no•-ƛ noN) liftρ liftγ prefix′ inner
world-coherent-right-source-all-lambda-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    okBlame@(ok-no no•-blame) noN liftρ liftγ
    (allocation-prefixᵀ prefix′ inner N⊢ N′⊢) =
  sourceAllAllocationPrefixCase cases
    prefix coherent exclusive unique wfR okBlame
    (ƛ _) (no•-ƛ noN) liftρ liftγ prefix′ inner
world-coherent-right-source-all-lambda-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    ok•@(ok-• vV′ noV′) noN liftρ liftγ rel =
  sourceAllTargetBullet (sourceAllResidualCases cases)
    prefix coherent exclusive unique wfR ok•
    (ƛ _) (no•-ƛ noN) liftρ liftγ rel
world-coherent-right-source-all-lambda-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    okApp@(ok-·₁ okL′ noM′) noN liftρ liftγ
    (allocation-prefixᵀ prefix′ inner N⊢ N′⊢) =
  sourceAllAllocationPrefixCase cases
    prefix coherent exclusive unique wfR okApp
    (ƛ _) (no•-ƛ noN) liftρ liftγ prefix′ inner
world-coherent-right-source-all-lambda-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    okApp@(ok-·₂ vL′ noL′ okM′) noN liftρ liftγ
    (allocation-prefixᵀ prefix′ inner N⊢ N′⊢) =
  sourceAllAllocationPrefixCase cases
    prefix coherent exclusive unique wfR okApp
    (ƛ _) (no•-ƛ noN) liftρ liftγ prefix′ inner
world-coherent-right-source-all-lambda-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    okν@(ok-ν okN′) noN liftρ liftγ rel =
  sourceAllTargetAllocation (sourceAllResidualCases cases)
    prefix coherent exclusive unique wfR okν
    (ƛ _) (no•-ƛ noN) liftρ liftγ rel
world-coherent-right-source-all-lambda-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    okPlus@(ok-⊕₁ okL′ noM′) noN liftρ liftγ
    (allocation-prefixᵀ prefix′ inner N⊢ N′⊢) =
  sourceAllAllocationPrefixCase cases
    prefix coherent exclusive unique wfR okPlus
    (ƛ _) (no•-ƛ noN) liftρ liftγ prefix′ inner
world-coherent-right-source-all-lambda-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    okPlus@(ok-⊕₂ vL′ noL′ okM′) noN liftρ liftγ
    (allocation-prefixᵀ prefix′ inner N⊢ N′⊢) =
  sourceAllAllocationPrefixCase cases
    prefix coherent exclusive unique wfR okPlus
    (ƛ _) (no•-ƛ noN) liftρ liftγ prefix′ inner
world-coherent-right-source-all-lambda-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    ok-cast@(ok-⟨⟩ okN′) noN liftρ liftγ
    (allocation-prefixᵀ prefix′ inner N⊢ N′⊢) =
  sourceAllAllocationPrefixCase cases
    prefix coherent exclusive unique wfR ok-cast
    (ƛ _) (no•-ƛ noN) liftρ liftγ prefix′ inner
world-coherent-right-source-all-lambda-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    ok-cast@(ok-⟨⟩ okN′) noN liftρ liftγ
    (⊑cast⊒ᵀ mode seal★ c⊒ inner q) =
  sourceAllTargetNarrowFrameCase cases
    prefix coherent exclusive unique wfR ok-cast
    (ƛ _) (no•-ƛ noN) mode seal★ c⊒ liftρ liftγ inner
world-coherent-right-source-all-lambda-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    ok-cast@(ok-⟨⟩ okN′) noN liftρ liftγ
    (⊑cast⊑ᵀ mode seal★ c⊑ inner q) =
  sourceAllTargetWidenFrameCase cases
    prefix coherent exclusive unique wfR ok-cast
    (ƛ _) (no•-ƛ noN) mode seal★ c⊑ liftρ liftγ inner
world-coherent-right-source-all-lambda-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    ok-cast@(ok-⟨⟩ okN′) noN liftρ liftγ
    (⊑cast⊑idᵀ seal★ c⊑ inner q) =
  sourceAllTargetIdWidenFrameCase cases
    prefix coherent exclusive unique wfR ok-cast
    (ƛ _) (no•-ƛ noN) seal★ c⊑ liftρ liftγ inner
world-coherent-right-source-all-lambda-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    ok-cast@(ok-⟨⟩ okN′) noN liftρ liftγ
    (⊑conv↑ᵀ c↑ inner q) =
  sourceAllTargetRevealFrameCase cases
    prefix coherent exclusive unique wfR ok-cast
    (ƛ _) (no•-ƛ noN) c↑ liftρ liftγ inner
world-coherent-right-source-all-lambda-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    ok-cast@(ok-⟨⟩ okN′) noN liftρ liftγ
    (⊑conv↓ᵀ c↓ inner q) =
  sourceAllTargetConcealFrameCase cases
    prefix coherent exclusive unique wfR ok-cast
    (ƛ _) (no•-ƛ noN) c↓ liftρ liftγ inner

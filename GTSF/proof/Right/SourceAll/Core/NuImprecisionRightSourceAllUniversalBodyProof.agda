module
  proof.Right.SourceAll.Core.NuImprecisionRightSourceAllUniversalBodyProof
  where

-- File Charter:
--   * Proves the nested-type-abstraction body case of source-universal
--     right-value closing from the flat source-all case capabilities.
--   * Splits target runtime syntax before QTI and delegates the genuine
--     nested source-only branch to its explicit residual capability.
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
  ; Λ_
  ; $
  )
open import QuotientedTermImprecision using
  ( allocation-prefixᵀ
  ; Λ⊑Λᵀ
  ; Λ⊑instβᵀ
  ; Λ⊑ᵀ
  ; ⊑cast⊒ᵀ
  ; ⊑cast⊑idᵀ
  ; ⊑cast⊑ᵀ
  ; ⊑conv↑ᵀ
  ; ⊑conv↓ᵀ
  )
open import
  proof.Right.SourceAll.ClosingValues.NuImprecisionRightSourceAllClosingCasesDef
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
  proof.Right.SourceAll.Core.NuImprecisionRightSourceAllResidualCasesDef
  using
  ( sourceAllNestedSourceAll
  ; sourceAllTargetAllocation
  ; sourceAllTargetBullet
  )
open import
  proof.Right.SourceAll.Core.NuImprecisionRightSourceAllUniversalBodyDef
  using (WorldCoherentRightSourceAllUniversalBodyᵀ)


world-coherent-right-source-all-universal-body-proofᵀ :
  WorldCoherentRightSourceAllClosingCases →
  WorldCoherentRightSourceAllUniversalBodyᵀ
world-coherent-right-source-all-universal-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    (ok-no (no•-ƛ noN′)) vU noU liftρ liftγ rel =
  sourceAllTerminalCase cases prefix coherent exclusive unique wfR
    (Λ vU) (no•-Λ noU) (ƛ _) (no•-ƛ noN′)
    liftρ liftγ rel
world-coherent-right-source-all-universal-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    (ok-no no•-$) vU noU liftρ liftγ rel =
  sourceAllTerminalCase cases prefix coherent exclusive unique wfR
    (Λ vU) (no•-Λ noU) ($ _) no•-$ liftρ liftγ rel
world-coherent-right-source-all-universal-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    okΛ@(ok-no (no•-Λ noU′)) vU noU liftρ liftγ
    rel@(Λ⊑Λᵀ liftρ′ liftγ′ vW vW′ body) =
  sourceAllTerminalCase cases prefix coherent exclusive unique wfR
    (Λ vU) (no•-Λ noU) (Λ vW′) (no•-Λ noU′)
    liftρ liftγ rel
world-coherent-right-source-all-universal-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    okΛ@(ok-no (no•-Λ noU′)) vU noU liftρ liftγ
    (Λ⊑ᵀ inner-occ liftρ′ liftγ′ vW body) =
  sourceAllNestedSourceAll (sourceAllResidualCases cases)
    prefix coherent exclusive unique wfR okΛ vW noU
    liftρ liftγ liftρ′ liftγ′ body
world-coherent-right-source-all-universal-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    okΛ@(ok-no (no•-Λ noU′)) vU noU liftρ liftγ
    (allocation-prefixᵀ prefix′ inner U⊢ N′⊢) =
  sourceAllAllocationPrefixCase cases
    prefix coherent exclusive unique wfR okΛ
    (Λ vU) (no•-Λ noU) liftρ liftγ prefix′ inner
world-coherent-right-source-all-universal-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    ok-cast@(ok-no (no•-⟨⟩ noN′)) vU noU liftρ liftγ
    (Λ⊑ᵀ inner-occ liftρ′ liftγ′ vW body) =
  sourceAllNestedSourceAll (sourceAllResidualCases cases)
    prefix coherent exclusive unique wfR ok-cast vW noU
    liftρ liftγ liftρ′ liftγ′ body
world-coherent-right-source-all-universal-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    (ok-no (no•-⟨⟩ noN′)) vU noU liftρ liftγ
    rel@(Λ⊑instβᵀ
      prefix₀ mode seal★ inst⊑ liftρ∀ liftρᴿ
      vW noW vW′ noW′ inert body f assm hτ hσ store-emb
      source-eq target-eq source-type-eq target-type-eq
      outer-index final-v final-no final-closed
      final-v′ final-no′ final-closed′
      source-typing target-typing) =
  sourceAllTerminalCase cases prefix coherent exclusive unique wfR
    (Λ vU) (no•-Λ noU) final-v′ final-no′
    liftρ liftγ rel
world-coherent-right-source-all-universal-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    ok-cast@(ok-no (no•-⟨⟩ noN′)) vU noU liftρ liftγ
    (allocation-prefixᵀ prefix′ inner U⊢ N′⊢) =
  sourceAllAllocationPrefixCase cases
    prefix coherent exclusive unique wfR ok-cast
    (Λ vU) (no•-Λ noU) liftρ liftγ prefix′ inner
world-coherent-right-source-all-universal-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    ok-cast@(ok-no (no•-⟨⟩ noN′)) vU noU liftρ liftγ
    (⊑cast⊒ᵀ mode seal★ c⊒ inner q) =
  sourceAllTargetNarrowFrameCase cases
    prefix coherent exclusive unique wfR ok-cast
    (Λ vU) (no•-Λ noU) mode seal★ c⊒ liftρ liftγ inner
world-coherent-right-source-all-universal-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    ok-cast@(ok-no (no•-⟨⟩ noN′)) vU noU liftρ liftγ
    (⊑cast⊑ᵀ mode seal★ c⊑ inner q) =
  sourceAllTargetWidenFrameCase cases
    prefix coherent exclusive unique wfR ok-cast
    (Λ vU) (no•-Λ noU) mode seal★ c⊑ liftρ liftγ inner
world-coherent-right-source-all-universal-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    ok-cast@(ok-no (no•-⟨⟩ noN′)) vU noU liftρ liftγ
    (⊑cast⊑idᵀ seal★ c⊑ inner q) =
  sourceAllTargetIdWidenFrameCase cases
    prefix coherent exclusive unique wfR ok-cast
    (Λ vU) (no•-Λ noU) seal★ c⊑ liftρ liftγ inner
world-coherent-right-source-all-universal-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    ok-cast@(ok-no (no•-⟨⟩ noN′)) vU noU liftρ liftγ
    (⊑conv↑ᵀ c↑ inner q) =
  sourceAllTargetRevealFrameCase cases
    prefix coherent exclusive unique wfR ok-cast
    (Λ vU) (no•-Λ noU) c↑ liftρ liftγ inner
world-coherent-right-source-all-universal-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    ok-cast@(ok-no (no•-⟨⟩ noN′)) vU noU liftρ liftγ
    (⊑conv↓ᵀ c↓ inner q) =
  sourceAllTargetConcealFrameCase cases
    prefix coherent exclusive unique wfR ok-cast
    (Λ vU) (no•-Λ noU) c↓ liftρ liftγ inner
world-coherent-right-source-all-universal-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    okν@(ok-no (no•-ν noN′)) vU noU liftρ liftγ rel =
  sourceAllTargetAllocation (sourceAllResidualCases cases)
    prefix coherent exclusive unique wfR okν
    (Λ vU) (no•-Λ noU) liftρ liftγ rel
world-coherent-right-source-all-universal-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    okVar@(ok-no no•-`) vU noU liftρ liftγ
    (Λ⊑ᵀ inner-occ liftρ′ liftγ′ vW body) =
  sourceAllNestedSourceAll (sourceAllResidualCases cases)
    prefix coherent exclusive unique wfR okVar vW noU
    liftρ liftγ liftρ′ liftγ′ body
world-coherent-right-source-all-universal-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    okVar@(ok-no no•-`) vU noU liftρ liftγ
    (allocation-prefixᵀ prefix′ inner U⊢ N′⊢) =
  sourceAllAllocationPrefixCase cases
    prefix coherent exclusive unique wfR okVar
    (Λ vU) (no•-Λ noU) liftρ liftγ prefix′ inner
world-coherent-right-source-all-universal-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    okApp@(ok-no (no•-· noL′ noM′))
    vU noU liftρ liftγ
    (Λ⊑ᵀ inner-occ liftρ′ liftγ′ vW body) =
  sourceAllNestedSourceAll (sourceAllResidualCases cases)
    prefix coherent exclusive unique wfR okApp vW noU
    liftρ liftγ liftρ′ liftγ′ body
world-coherent-right-source-all-universal-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    okApp@(ok-no (no•-· noL′ noM′))
    vU noU liftρ liftγ
    (allocation-prefixᵀ prefix′ inner U⊢ N′⊢) =
  sourceAllAllocationPrefixCase cases
    prefix coherent exclusive unique wfR okApp
    (Λ vU) (no•-Λ noU) liftρ liftγ prefix′ inner
world-coherent-right-source-all-universal-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    okPlus@(ok-no (no•-⊕ noL′ noM′))
    vU noU liftρ liftγ
    (Λ⊑ᵀ inner-occ liftρ′ liftγ′ vW body) =
  sourceAllNestedSourceAll (sourceAllResidualCases cases)
    prefix coherent exclusive unique wfR okPlus vW noU
    liftρ liftγ liftρ′ liftγ′ body
world-coherent-right-source-all-universal-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    okPlus@(ok-no (no•-⊕ noL′ noM′))
    vU noU liftρ liftγ
    (allocation-prefixᵀ prefix′ inner U⊢ N′⊢) =
  sourceAllAllocationPrefixCase cases
    prefix coherent exclusive unique wfR okPlus
    (Λ vU) (no•-Λ noU) liftρ liftγ prefix′ inner
world-coherent-right-source-all-universal-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    okBlame@(ok-no no•-blame) vU noU liftρ liftγ
    (Λ⊑ᵀ inner-occ liftρ′ liftγ′ vW body) =
  sourceAllNestedSourceAll (sourceAllResidualCases cases)
    prefix coherent exclusive unique wfR okBlame vW noU
    liftρ liftγ liftρ′ liftγ′ body
world-coherent-right-source-all-universal-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    okBlame@(ok-no no•-blame) vU noU liftρ liftγ
    (allocation-prefixᵀ prefix′ inner U⊢ N′⊢) =
  sourceAllAllocationPrefixCase cases
    prefix coherent exclusive unique wfR okBlame
    (Λ vU) (no•-Λ noU) liftρ liftγ prefix′ inner
world-coherent-right-source-all-universal-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    ok•@(ok-• vV′ noV′) vU noU liftρ liftγ rel =
  sourceAllTargetBullet (sourceAllResidualCases cases)
    prefix coherent exclusive unique wfR ok•
    (Λ vU) (no•-Λ noU) liftρ liftγ rel
world-coherent-right-source-all-universal-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    okApp@(ok-·₁ okL′ noM′) vU noU liftρ liftγ
    (Λ⊑ᵀ inner-occ liftρ′ liftγ′ vW body) =
  sourceAllNestedSourceAll (sourceAllResidualCases cases)
    prefix coherent exclusive unique wfR okApp vW noU
    liftρ liftγ liftρ′ liftγ′ body
world-coherent-right-source-all-universal-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    okApp@(ok-·₁ okL′ noM′) vU noU liftρ liftγ
    (allocation-prefixᵀ prefix′ inner U⊢ N′⊢) =
  sourceAllAllocationPrefixCase cases
    prefix coherent exclusive unique wfR okApp
    (Λ vU) (no•-Λ noU) liftρ liftγ prefix′ inner
world-coherent-right-source-all-universal-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    okApp@(ok-·₂ vL′ noL′ okM′)
    vU noU liftρ liftγ
    (Λ⊑ᵀ inner-occ liftρ′ liftγ′ vW body) =
  sourceAllNestedSourceAll (sourceAllResidualCases cases)
    prefix coherent exclusive unique wfR okApp vW noU
    liftρ liftγ liftρ′ liftγ′ body
world-coherent-right-source-all-universal-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    okApp@(ok-·₂ vL′ noL′ okM′)
    vU noU liftρ liftγ
    (allocation-prefixᵀ prefix′ inner U⊢ N′⊢) =
  sourceAllAllocationPrefixCase cases
    prefix coherent exclusive unique wfR okApp
    (Λ vU) (no•-Λ noU) liftρ liftγ prefix′ inner
world-coherent-right-source-all-universal-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    okν@(ok-ν okN′) vU noU liftρ liftγ rel =
  sourceAllTargetAllocation (sourceAllResidualCases cases)
    prefix coherent exclusive unique wfR okν
    (Λ vU) (no•-Λ noU) liftρ liftγ rel
world-coherent-right-source-all-universal-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    okPlus@(ok-⊕₁ okL′ noM′) vU noU liftρ liftγ
    (Λ⊑ᵀ inner-occ liftρ′ liftγ′ vW body) =
  sourceAllNestedSourceAll (sourceAllResidualCases cases)
    prefix coherent exclusive unique wfR okPlus vW noU
    liftρ liftγ liftρ′ liftγ′ body
world-coherent-right-source-all-universal-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    okPlus@(ok-⊕₁ okL′ noM′) vU noU liftρ liftγ
    (allocation-prefixᵀ prefix′ inner U⊢ N′⊢) =
  sourceAllAllocationPrefixCase cases
    prefix coherent exclusive unique wfR okPlus
    (Λ vU) (no•-Λ noU) liftρ liftγ prefix′ inner
world-coherent-right-source-all-universal-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    okPlus@(ok-⊕₂ vL′ noL′ okM′)
    vU noU liftρ liftγ
    (Λ⊑ᵀ inner-occ liftρ′ liftγ′ vW body) =
  sourceAllNestedSourceAll (sourceAllResidualCases cases)
    prefix coherent exclusive unique wfR okPlus vW noU
    liftρ liftγ liftρ′ liftγ′ body
world-coherent-right-source-all-universal-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    okPlus@(ok-⊕₂ vL′ noL′ okM′)
    vU noU liftρ liftγ
    (allocation-prefixᵀ prefix′ inner U⊢ N′⊢) =
  sourceAllAllocationPrefixCase cases
    prefix coherent exclusive unique wfR okPlus
    (Λ vU) (no•-Λ noU) liftρ liftγ prefix′ inner
world-coherent-right-source-all-universal-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    ok-cast@(ok-⟨⟩ okN′) vU noU liftρ liftγ
    (Λ⊑ᵀ inner-occ liftρ′ liftγ′ vW body) =
  sourceAllNestedSourceAll (sourceAllResidualCases cases)
    prefix coherent exclusive unique wfR ok-cast vW noU
    liftρ liftγ liftρ′ liftγ′ body
world-coherent-right-source-all-universal-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    (ok-⟨⟩ okN′) vU noU liftρ liftγ
    rel@(Λ⊑instβᵀ
      prefix₀ mode seal★ inst⊑ liftρ∀ liftρᴿ
      vW noW vW′ noW′ inert body f assm hτ hσ store-emb
      source-eq target-eq source-type-eq target-type-eq
      outer-index final-v final-no final-closed
      final-v′ final-no′ final-closed′
      source-typing target-typing) =
  sourceAllTerminalCase cases prefix coherent exclusive unique wfR
    (Λ vU) (no•-Λ noU) final-v′ final-no′
    liftρ liftγ rel
world-coherent-right-source-all-universal-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    ok-cast@(ok-⟨⟩ okN′) vU noU liftρ liftγ
    (allocation-prefixᵀ prefix′ inner U⊢ N′⊢) =
  sourceAllAllocationPrefixCase cases
    prefix coherent exclusive unique wfR ok-cast
    (Λ vU) (no•-Λ noU) liftρ liftγ prefix′ inner
world-coherent-right-source-all-universal-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    ok-cast@(ok-⟨⟩ okN′) vU noU liftρ liftγ
    (⊑cast⊒ᵀ mode seal★ c⊒ inner q) =
  sourceAllTargetNarrowFrameCase cases
    prefix coherent exclusive unique wfR ok-cast
    (Λ vU) (no•-Λ noU) mode seal★ c⊒ liftρ liftγ inner
world-coherent-right-source-all-universal-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    ok-cast@(ok-⟨⟩ okN′) vU noU liftρ liftγ
    (⊑cast⊑ᵀ mode seal★ c⊑ inner q) =
  sourceAllTargetWidenFrameCase cases
    prefix coherent exclusive unique wfR ok-cast
    (Λ vU) (no•-Λ noU) mode seal★ c⊑ liftρ liftγ inner
world-coherent-right-source-all-universal-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    ok-cast@(ok-⟨⟩ okN′) vU noU liftρ liftγ
    (⊑cast⊑idᵀ seal★ c⊑ inner q) =
  sourceAllTargetIdWidenFrameCase cases
    prefix coherent exclusive unique wfR ok-cast
    (Λ vU) (no•-Λ noU) seal★ c⊑ liftρ liftγ inner
world-coherent-right-source-all-universal-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    ok-cast@(ok-⟨⟩ okN′) vU noU liftρ liftγ
    (⊑conv↑ᵀ c↑ inner q) =
  sourceAllTargetRevealFrameCase cases
    prefix coherent exclusive unique wfR ok-cast
    (Λ vU) (no•-Λ noU) c↑ liftρ liftγ inner
world-coherent-right-source-all-universal-body-proofᵀ
    cases prefix coherent exclusive unique wfR
    ok-cast@(ok-⟨⟩ okN′) vU noU liftρ liftγ
    (⊑conv↓ᵀ c↓ inner q) =
  sourceAllTargetConcealFrameCase cases
    prefix coherent exclusive unique wfR ok-cast
    (Λ vU) (no•-Λ noU) c↓ liftρ liftγ inner

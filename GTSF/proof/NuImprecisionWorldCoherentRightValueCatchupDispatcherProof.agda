module
  proof.NuImprecisionWorldCoherentRightValueCatchupDispatcherProof
  where

-- File Charter:
--   * Assembles the eight right-value catch-up capabilities into the frozen
--     ambient-prefix worker.
--   * Recurses structurally on same-world inner imprecision derivations and
--     handles relational-store allocation prefixes directly by transitivity.
--   * Dispatches the two cross-index binder cases to their explicit closing
--     capabilities instead of passing the recursive function as an argument.
--   * Contains no semantic case implementation, postulate, hole, incomplete
--     match, or permissive option.

open import NuTerms using
  ( no•-Λ
  ; no•-⟨⟩
  ; ƛ_
  ; Λ_
  ; $
  ; _⟨_⟩
  )
open import NuTermImprecision using
  (lift-left-ctx-[]; lift-right-ctx-[])
open import QuotientedTermImprecision using
  ( allocation-prefixᵀ
  ; blame⊑ᵀ
  ; cast⊒⊑ᵀ
  ; cast⊑⊑ᵀ
  ; conv↑⊑ᵀ
  ; conv↓⊑ᵀ
  ; conv⊑convᵀ
  ; down⊑downᵀ
  ; gen⊑groundᵀ
  ; gen-down⊑gen-downᵀ
  ; up⊑upᵀ
  ; x⊑xᵀ
  ; α⊑αᵀ
  ; α⊑ᵀ
  ; Λ⊑Λᵀ
  ; Λ⊑ᵀ
  ; νcast⊑νcastᵀ
  ; νcast⊑ᵀ
  ; ν⊑νᵀ
  ; ν⊑ᵀ
  ; κ⊑κᵀ
  ; ·⊑·ᵀ
  ; ⊑cast⊒ᵀ
  ; ⊑cast⊑idᵀ
  ; ⊑cast⊑ᵀ
  ; ⊑conv↑ᵀ
  ; ⊑conv↓ᵀ
  ; ⊑αᵀ
  ; ⊑νcastᵀ
  ; ⊑νᵀ
  ; ⊕⊑⊕ᵀ
  ; ƛ⊑ƛᵀ
  )
open import proof.NuImprecisionStorePrefix using
  (store-imp-prefix-transⁱ)
open import proof.NuProgress using (runtime-value-no•)
open import
  proof.NuImprecisionWorldCoherentRightValueCatchupCasesDef
  using
  ( WorldCoherentRightValueCatchupCases
  ; rightValuePairedCastFrameCase
  ; rightValueQuotientDownUpFrameCase
  ; rightValueSourceAllClosingCase
  ; rightValueSourceFramesCase
  ; rightValueTargetAllocationFramesCase
  ; rightValueTargetBulletClosingCase
  ; rightValueTargetCastTerminalizationCase
  ; rightValueTerminalCase
  )
open import
  proof.NuImprecisionWorldCoherentRightQuotientDownUpFrameDef
  using
  ( rightQuotientGenDownUpFrame
  ; rightQuotientIdDownUpFrame
  )
open import proof.NuImprecisionWorldCoherentRightSourceFramesDef using
  ( rightSourceConcealFrame
  ; rightSourceNarrowFrame
  ; rightSourceRevealFrame
  ; rightSourceWidenFrame
  )
open import
  proof.NuImprecisionWorldCoherentRightTargetAllocationFramesDef
  using (rightTargetNuCastFrame; rightTargetNuFrame)
open import
  proof.NuImprecisionWorldCoherentRightTargetCastTerminalizationDef using
  ( rightTargetConcealFrame
  ; rightTargetIdWidenFrame
  ; rightTargetNarrowFrame
  ; rightTargetRevealFrame
  ; rightTargetWidenFrame
  )
open import
  proof.NuImprecisionWorldCoherentRightValueCatchupPrefixDef
  using (WorldCoherentRightValueCatchupPrefixᵀ)
open import proof.NuPreservation using (runtime-⟨⟩; runtime-ν)


world-coherent-right-value-catchup-dispatcher-proofᵀ :
  WorldCoherentRightValueCatchupCases →
  WorldCoherentRightValueCatchupPrefixᵀ
world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR okM′ () noV
    (blame⊑ᵀ M′⊢)
world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR okM′ () noV
    (x⊑xᵀ x∈)
world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR (NuTerms.ok-no noV′)
    vV noV rel@(ƛ⊑ƛᵀ hA hA′ body) =
  rightValueTerminalCase cases prefix coherent exclusive unique wfR
    vV noV (ƛ _) noV′ rel
world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR okM′ () noV
    (·⊑·ᵀ L⊑L′ M⊑M′)
world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR okM′
    ((vM ⟨ inert-d ⟩) ⟨ inert-u ⟩)
    (no•-⟨⟩ (no•-⟨⟩ noM))
    (up⊑upᵀ (down⊑downᵀ d⊒ d′⊒ M⊑M′ qD)
      widening pA) =
  rightQuotientIdDownUpFrame quotient-cases
    prefix coherent exclusive unique wfR okM′ vM noM inert-d inert-u
    d⊒ d′⊒ qD M⊑M′ widening inner
  where
  quotient-cases = rightValueQuotientDownUpFrameCase cases
  inner = world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR
    (runtime-⟨⟩ (runtime-⟨⟩ okM′)) vM noM M⊑M′
world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR okM′
    ((vM ⟨ inert-d ⟩) ⟨ inert-u ⟩)
    (no•-⟨⟩ (no•-⟨⟩ noM))
    (up⊑upᵀ (gen-down⊑gen-downᵀ d⊒ d′⊒ M⊑M′ qD)
      widening pA) =
  rightQuotientGenDownUpFrame quotient-cases
    prefix coherent exclusive unique wfR okM′ vM noM inert-d inert-u
    d⊒ d′⊒ qD M⊑M′ widening inner
  where
  quotient-cases = rightValueQuotientDownUpFrameCase cases
  inner = world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR
    (runtime-⟨⟩ (runtime-⟨⟩ okM′)) vM noM M⊑M′
world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR (NuTerms.ok-no noV′)
    vV noV rel@(Λ⊑Λᵀ liftρ liftγ vW vW′ body) =
  rightValueTerminalCase cases prefix coherent exclusive unique wfR
    vV noV (Λ vW′) noV′ rel
world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR okN′
    (Λ vW) (no•-Λ noW)
    (Λ⊑ᵀ occ liftρ lift-left-ctx-[] vV V⊑N′) =
  rightValueSourceAllClosingCase cases prefix coherent exclusive unique wfR
    okN′ vV noW liftρ lift-left-ctx-[] V⊑N′
world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR okM′ () noV
    (α⊑αᵀ vL noL vL′ noL′ pA liftρ liftγ
      L⊑L′ L•⊢ L′•⊢)
world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR okM′ () noV
    (α⊑ᵀ vL noL hA liftρ liftγ L⊑M′ L•⊢ M′⊢)
world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR okL′• vN noN
    (⊑αᵀ vL′ noL′ hA liftρ lift-right-ctx-[]
      N⊑L′ r N⊢ L′•⊢) =
  rightValueTargetBulletClosingCase cases hA prefix coherent exclusive unique
    wfR okL′• vN noN vL′ noL′ liftρ lift-right-ctx-[]
    N⊑L′ N⊢ L′•⊢
world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR okM′ vV noV
    (allocation-prefixᵀ prefix₀ inner M⊢ M′⊢) =
  world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases (store-imp-prefix-transⁱ prefix₀ prefix)
    coherent exclusive unique wfR okM′ vV noV inner
world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR okM′ () noV
    (ν⊑νᵀ hA hA′ s↑ s′↑ pA pA⇑ liftρ liftγ N⊑N′)
world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR okM′ () noV
    (ν⊑ᵀ hA h⇑A s↑ liftρ liftγ N⊑M′)
world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR okν vN noN
    (⊑νᵀ hA h⇑A s↑ liftρ lift-right-ctx-[] r N⊑N′) =
  rightTargetNuFrame allocation-cases prefix coherent exclusive unique wfR
    okν vN noN hA h⇑A s↑ liftρ lift-right-ctx-[] r N⊑N′ inner
  where
  allocation-cases = rightValueTargetAllocationFramesCase cases
  inner = world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR (runtime-ν okν)
    vN noN N⊑N′
world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR okM′ () noV
    (νcast⊑νcastᵀ mode seal★ mode′ seal★′
      s⊑ s′⊑ compat liftρ liftγ N⊑N′)
world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR okM′ () noV
    (νcast⊑ᵀ mode seal★ s⊑ liftρ liftγ N⊑M′)
world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR okν vN noN
    (⊑νcastᵀ mode seal★ s⊑ liftρ lift-right-ctx-[] r N⊑N′) =
  rightTargetNuCastFrame allocation-cases prefix coherent exclusive unique wfR
    okν vN noN mode seal★ s⊑ liftρ lift-right-ctx-[] r N⊑N′ inner
  where
  allocation-cases = rightValueTargetAllocationFramesCase cases
  inner = world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR (runtime-ν okν)
    vN noN N⊑N′
world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR (NuTerms.ok-no noV′)
    vV noV rel@κ⊑κᵀ =
  rightValueTerminalCase cases prefix coherent exclusive unique wfR
    vV noV ($ _) noV′ rel
world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR okM′ () noV
    (⊕⊑⊕ᵀ L⊑L′ M⊑M′)
world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR okW
    vSource noSource
    rel@(gen⊑groundᵀ mode seal★ c⊒ gH vV vW W⊢ V⊑Wtag q) =
  rightValueTerminalCase cases prefix coherent exclusive unique wfR
    vSource noSource vW (runtime-value-no• okW vW) rel
world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR okM′
    (vM ⟨ inert ⟩) (no•-⟨⟩ noM)
    (cast⊒⊑ᵀ mode seal★ c⊒ M⊑M′ q) =
  rightSourceNarrowFrame source-cases prefix coherent exclusive unique wfR
    okM′ vM noM inert mode seal★ c⊒ M⊑M′ inner
  where
  source-cases = rightValueSourceFramesCase cases
  inner = world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR okM′ vM noM M⊑M′
world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR okM′
    (vM ⟨ inert ⟩) (no•-⟨⟩ noM)
    (cast⊑⊑ᵀ mode seal★ c⊑ M⊑M′ q) =
  rightSourceWidenFrame source-cases prefix coherent exclusive unique wfR
    okM′ vM noM inert mode seal★ c⊑ M⊑M′ inner
  where
  source-cases = rightValueSourceFramesCase cases
  inner = world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR okM′ vM noM M⊑M′
world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR okM′ vV noV
    (⊑cast⊒ᵀ mode seal★ c⊒ V⊑M′ q) =
  rightTargetNarrowFrame target-cases prefix coherent exclusive unique wfR
    okM′ vV noV mode seal★ c⊒ V⊑M′ inner
  where
  target-cases = rightValueTargetCastTerminalizationCase cases
  inner = world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR (runtime-⟨⟩ okM′)
    vV noV V⊑M′
world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR okM′ vV noV
    (⊑cast⊑ᵀ mode seal★ c⊑ V⊑M′ q) =
  rightTargetWidenFrame target-cases prefix coherent exclusive unique wfR
    okM′ vV noV mode seal★ c⊑ V⊑M′ inner
  where
  target-cases = rightValueTargetCastTerminalizationCase cases
  inner = world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR (runtime-⟨⟩ okM′)
    vV noV V⊑M′
world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR okM′ vV noV
    (⊑cast⊑idᵀ seal★ c⊑ V⊑M′ q) =
  rightTargetIdWidenFrame target-cases prefix coherent exclusive unique wfR
    okM′ vV noV seal★ c⊑ V⊑M′ inner
  where
  target-cases = rightValueTargetCastTerminalizationCase cases
  inner = world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR (runtime-⟨⟩ okM′)
    vV noV V⊑M′
world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR okM′
    (vM ⟨ inert ⟩) (no•-⟨⟩ noM)
    (conv⊑convᵀ paired M⊑M′) =
  rightValuePairedCastFrameCase cases prefix coherent exclusive unique wfR
    okM′ vM noM inert paired M⊑M′ inner
  where
  inner = world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR (runtime-⟨⟩ okM′)
    vM noM M⊑M′
world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR okM′
    (vM ⟨ inert ⟩) (no•-⟨⟩ noM)
    (conv↑⊑ᵀ c↑ M⊑M′ q) =
  rightSourceRevealFrame source-cases prefix coherent exclusive unique wfR
    okM′ vM noM inert c↑ M⊑M′ inner
  where
  source-cases = rightValueSourceFramesCase cases
  inner = world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR okM′ vM noM M⊑M′
world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR okM′
    (vM ⟨ inert ⟩) (no•-⟨⟩ noM)
    (conv↓⊑ᵀ c↓ M⊑M′ q) =
  rightSourceConcealFrame source-cases prefix coherent exclusive unique wfR
    okM′ vM noM inert c↓ M⊑M′ inner
  where
  source-cases = rightValueSourceFramesCase cases
  inner = world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR okM′ vM noM M⊑M′
world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR okM′ vV noV
    (⊑conv↑ᵀ c↑ V⊑M′ q) =
  rightTargetRevealFrame target-cases prefix coherent exclusive unique wfR
    okM′ vV noV c↑ V⊑M′ inner
  where
  target-cases = rightValueTargetCastTerminalizationCase cases
  inner = world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR (runtime-⟨⟩ okM′)
    vV noV V⊑M′
world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR okM′ vV noV
    (⊑conv↓ᵀ c↓ V⊑M′ q) =
  rightTargetConcealFrame target-cases prefix coherent exclusive unique wfR
    okM′ vV noV c↓ V⊑M′ inner
  where
  target-cases = rightValueTargetCastTerminalizationCase cases
  inner = world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR (runtime-⟨⟩ okM′)
    vV noV V⊑M′

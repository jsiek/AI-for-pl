module
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightValueCatchupDispatcherProof
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
open import proof.NuCore.Relations.NuImprecisionTermContextDef using
  ( lift-left-ctx-[]
  ; lift-right-ctx-[]
  )
open import QuotientedTermImprecision using
  ( allocation-prefixᵀ
  ; blame⊑ᵀ
  ; cast⊒⊑ᵀ
  ; cast⊑⊑ᵀ
  ; closeᵀ
  ; conv↑⊑ᵀ
  ; conv↓⊑ᵀ
  ; gen⊑groundᵀ
  ; paired-downᵀ
  ; x⊑xᵀ
  ; α⊑αᵀ
  ; α⊑ᵀ
  ; Λ⊑Λᵀ
  ; Λ⊑ᵀ
  ; target-instantiationᵀ
  ; paired-concealᵀ
  ; paired-revealᵀ
  ; paired-wideningᵀ
  ; ν⊑νᵀ
  ; ν⊑ᵀ
  ; κ⊑κᵀ
  ; ·⊑·ᵀ
  ; ⊑cast⊒ᵀ
  ; ⊑cast⊑ᵀ
  ; ⊑conv↑ᵀ
  ; ⊑conv↓ᵀ
  ; ⊕⊑⊕ᵀ
  ; ƛ⊑ƛᵀ
  )
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  (store-imp-prefix-transⁱ)
open import proof.DGG.Core.NuProgress using (runtime-value-no•)
open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightValueCatchupCasesDef
  using
  ( WorldCoherentRightValueCatchupCases
  ; rightValuePairedFrames
  ; rightValueQuotientDownUpFrameCase
  ; rightValueSourceAllClosingCase
  ; rightValueSourceFramesCase
  ; rightValueTargetAllocationFramesCase
  ; rightValueTargetBulletClosingCase
  ; rightValueTargetCastTerminalizationCase
  ; rightValueTerminalCase
  )
open import
  proof.WorldCoherent.Right.Core.NuImprecisionWorldCoherentRightPairedFramesDef
  using
  ( rightPairedConcealFrame
  ; rightPairedRevealFrame
  ; rightPairedWideningFrame
  )
open import
  proof.WorldCoherent.Right.Core.NuImprecisionWorldCoherentRightQuotientDownUpFrameDef
  using (rightQuotientDownUpFrame)
open import proof.WorldCoherent.Right.Source.Frames.NuImprecisionWorldCoherentRightSourceFramesDef using
  ( rightSourceConcealFrame
  ; rightSourceNarrowFrame
  ; rightSourceRevealFrame
  ; rightSourceWidenFrame
  )
open import
  proof.WorldCoherent.Right.Target.ActiveRoots.NuImprecisionWorldCoherentRightTargetAllocationFramesDef
  using (rightTargetNuCastFrame; rightTargetNuFrame)
open import
  proof.WorldCoherent.Right.Target.Terminalization.NuImprecisionWorldCoherentRightTargetCastTerminalizationDef using
  ( rightTargetConcealFrame
  ; rightTargetNarrowFrame
  ; rightTargetRevealFrame
  ; rightTargetWidenFrame
  )
open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightValueCatchupPrefixDef
  using (WorldCoherentRightValueCatchupPrefixᵀ)
open import proof.DGG.Core.NuPreservation using (runtime-⟨⟩; runtime-ν)
open import
  proof.Quotient.NuImprecisionEmbeddedTargetInstantiationCreationProperties
  using
  ( embedded-creation-target-no-bulletᴱ
  ; embedded-creation-target-valueᴱ
  )


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
    (closeᵀ
      (paired-downᵀ M⊑M′
        mode d⊒ d-shape mode′ d′⊒ d′-shape
        down-square down-compatible)
      widening pA u-shape u′-shape up-square up-compatible) =
  rightQuotientDownUpFrame quotient-cases
    prefix coherent exclusive unique wfR okM′
    vM noM inert-d inert-u M⊑M′
    mode d⊒ d-shape mode′ d′⊒ d′-shape
    down-square down-compatible
    widening u-shape u′-shape up-square up-compatible
    inner
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
    cases prefix coherent exclusive unique wfR okW′
    vV noV
    rel@(target-instantiationᵀ embedded) =
  rightValueTerminalCase cases prefix coherent exclusive unique wfR
    vV noV
    (embedded-creation-target-valueᴱ embedded)
    (embedded-creation-target-no-bulletᴱ embedded)
    rel
world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR okM′ () noV
    (α⊑αᵀ vL noL vL′ noL′ pA liftρ liftγ
      L⊑L′ L•⊢ L′•⊢)
world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR okM′ () noV
    (α⊑ᵀ vL noL hA liftρ liftγ L⊑M′ L•⊢ M′⊢)
world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR okM′ vV noV
    (allocation-prefixᵀ prefix₀ inner M⊢ M′⊢) =
  world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases (store-imp-prefix-transⁱ prefix₀ prefix)
    coherent exclusive unique wfR okM′ vV noV inner
world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR okM′ () noV
    (ν⊑νᵀ
      hA hA′ s↑ s′↑ pA pA⇑ liftρ liftγ N⊑N′ replacement)
world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR okM′ () noV
    (ν⊑ᵀ hA h⇑A s↑ liftρ liftγ N⊑M′ replacement)
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
    (cast⊒⊑ᵀ mode seal★ c⊒ M⊑M′ q c-shape comp) =
  rightSourceNarrowFrame source-cases prefix coherent exclusive unique wfR
    okM′ vM noM inert mode seal★ c⊒ c-shape comp M⊑M′ inner
  where
  source-cases = rightValueSourceFramesCase cases
  inner = world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR okM′ vM noM M⊑M′
world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR okM′
    (vM ⟨ inert ⟩) (no•-⟨⟩ noM)
    (cast⊑⊑ᵀ mode seal★ c⊑ M⊑M′ q c-shape comp) =
  rightSourceWidenFrame source-cases prefix coherent exclusive unique wfR
    okM′ vM noM inert mode seal★ c⊑ c-shape comp M⊑M′ inner
  where
  source-cases = rightValueSourceFramesCase cases
  inner = world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR okM′ vM noM M⊑M′
world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR okM′ vV noV
    (⊑cast⊒ᵀ mode seal★ c⊒ V⊑M′ q c-shape comp) =
  rightTargetNarrowFrame target-cases prefix coherent exclusive unique wfR
    okM′ vV noV mode seal★ c⊒ c-shape comp V⊑M′ inner
  where
  target-cases = rightValueTargetCastTerminalizationCase cases
  inner = world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR (runtime-⟨⟩ okM′)
    vV noV V⊑M′
world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR okM′ vV noV
    (⊑cast⊑ᵀ mode seal★ c⊑ V⊑M′ q c-shape comp) =
  rightTargetWidenFrame target-cases prefix coherent exclusive unique wfR
    okM′ vV noV mode seal★ c⊑ c-shape comp V⊑M′ inner
  where
  target-cases = rightValueTargetCastTerminalizationCase cases
  inner = world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR (runtime-⟨⟩ okM′)
    vV noV V⊑M′
world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR okM′
    (vM ⟨ inert ⟩) (no•-⟨⟩ noM)
    (paired-revealᵀ corr c↑ c′↑ replacement M⊑M′) =
  rightPairedRevealFrame paired-cases
    prefix coherent exclusive unique wfR okM′ vM noM inert
    corr c↑ c′↑ replacement M⊑M′ inner
  where
  paired-cases = rightValuePairedFrames cases
  inner = world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR (runtime-⟨⟩ okM′)
    vM noM M⊑M′
world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR okM′
    (vM ⟨ inert ⟩) (no•-⟨⟩ noM)
    (paired-concealᵀ corr c↓ c′↓ replacement M⊑M′) =
  rightPairedConcealFrame paired-cases
    prefix coherent exclusive unique wfR okM′ vM noM inert
    corr c↓ c′↓ replacement M⊑M′ inner
  where
  paired-cases = rightValuePairedFrames cases
  inner = world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR (runtime-⟨⟩ okM′)
    vM noM M⊑M′
world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR okM′
    (vM ⟨ inert ⟩) (no•-⟨⟩ noM)
    (paired-wideningᵀ
      mode seal★ c⊑ c-shape mode′ seal★′ c′⊑ c′-shape
      left-square right-square compatible M⊑M′) =
  rightPairedWideningFrame paired-cases
    prefix coherent exclusive unique wfR okM′ vM noM inert
    mode seal★ c⊑ c-shape mode′ seal★′ c′⊑ c′-shape
    left-square right-square compatible M⊑M′ inner
  where
  paired-cases = rightValuePairedFrames cases
  inner = world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR (runtime-⟨⟩ okM′)
    vM noM M⊑M′
world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR okM′
    (vM ⟨ inert ⟩) (no•-⟨⟩ noM)
    (conv↑⊑ᵀ c↑ M⊑M′ q replacement) =
  rightSourceRevealFrame source-cases prefix coherent exclusive unique wfR
    okM′ vM noM inert c↑ replacement M⊑M′ inner
  where
  source-cases = rightValueSourceFramesCase cases
  inner = world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR okM′ vM noM M⊑M′
world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR okM′
    (vM ⟨ inert ⟩) (no•-⟨⟩ noM)
    (conv↓⊑ᵀ c↓ M⊑M′ q replacement) =
  rightSourceConcealFrame source-cases prefix coherent exclusive unique wfR
    okM′ vM noM inert c↓ replacement M⊑M′ inner
  where
  source-cases = rightValueSourceFramesCase cases
  inner = world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR okM′ vM noM M⊑M′
world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR okM′ vV noV
    (⊑conv↑ᵀ c↑ V⊑M′ q replacement) =
  rightTargetRevealFrame target-cases prefix coherent exclusive unique wfR
    okM′ vV noV c↑ replacement V⊑M′ inner
  where
  target-cases = rightValueTargetCastTerminalizationCase cases
  inner = world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR (runtime-⟨⟩ okM′)
    vV noV V⊑M′
world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR okM′ vV noV
    (⊑conv↓ᵀ c↓ V⊑M′ q replacement) =
  rightTargetConcealFrame target-cases prefix coherent exclusive unique wfR
    okM′ vV noV c↓ replacement V⊑M′ inner
  where
  target-cases = rightValueTargetCastTerminalizationCase cases
  inner = world-coherent-right-value-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR (runtime-⟨⟩ okM′)
    vV noV V⊑M′

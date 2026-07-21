module
  proof.NuImprecisionWorldCoherentRightTargetPendingSequenceContinuationProof
  where

-- File Charter:
--   * Proves the three pending target-sequence continuations from an assumed
--     complete target-cast terminalization capability.
--   * Starts from the canonical zero-step value catch-up, then terminalizes
--     the first and second target casts in order.
--   * The stronger terminalization premise subsumes the hereditary plans and
--     rank equation at this higher-order fit boundary.
--   * Deliberately has no canonical Lemma: canonical assembly requires the
--     well-founded target-administration SCC.
--   * Contains no result, outcome, ranked carrier, alias, postulate, hole,
--     permissive option, compatibility shim, or termination bypass.

open import proof.NuPreservation using (runtime-⟨⟩)
open import QuotientedTermImprecision using
  ( prefix-reflⁱ
  ; ⊑cast⊒ᵀ
  ; ⊑cast⊑idᵀ
  ; ⊑cast⊑ᵀ
  )
open import
  proof.NuImprecisionWorldCoherentRightTargetCastTerminalizationDef
  using
  ( WorldCoherentRightTargetCastTerminalization
  ; rightTargetIdWidenFrame
  ; rightTargetNarrowFrame
  ; rightTargetWidenFrame
  )
open import
  proof.NuImprecisionWorldCoherentRightTargetPendingSequenceContinuationDef
  using
  ( WorldCoherentRightTargetPendingSequenceContinuation
  ; rightTargetPendingIdWidenSequence
  ; rightTargetPendingNarrowSequence
  ; rightTargetPendingWidenSequence
  )
open import proof.NuImprecisionWorldCoherentRightValueTerminalLemma using
  (world-coherent-right-value-terminalᵀ)


world-coherent-right-target-pending-sequence-continuation-proofᵀ :
  WorldCoherentRightTargetCastTerminalization →
  WorldCoherentRightTargetPendingSequenceContinuation
rightTargetPendingNarrowSequence
    (world-coherent-right-target-pending-sequence-continuation-proofᵀ
      terminalization)
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {ρ = ρ}
    {p = p} {r = r} {q = q}
    vW mode seal★ s⊒ t⊒ _ _ _ V⊑W
    coherent exclusive wfR runtime vV noV noW =
  rightTargetNarrowFrame terminalization
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {ρ₀ = ρ} {ρ⁺ = ρ} {p = r} {q = q}
    prefix-reflⁱ coherent exclusive wfR runtime
    vV noV mode seal★ t⊒ (⊑cast⊒ᵀ mode seal★ s⊒ V⊑W r)
    (rightTargetNarrowFrame terminalization
      {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      {ρ₀ = ρ} {ρ⁺ = ρ} {p = p} {q = r}
      prefix-reflⁱ coherent exclusive wfR
      (runtime-⟨⟩ runtime) vV noV mode seal★ s⊒ V⊑W
      (world-coherent-right-value-terminalᵀ
        {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
        {ρ₀ = ρ} {ρ⁺ = ρ} {p = p}
        prefix-reflⁱ coherent exclusive wfR
        vV noV vW noW V⊑W))
rightTargetPendingWidenSequence
    (world-coherent-right-target-pending-sequence-continuation-proofᵀ
      terminalization)
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {ρ = ρ}
    {p = p} {r = r} {q = q}
    vW mode seal★ s⊑ t⊑ _ _ _ V⊑W
    coherent exclusive wfR runtime vV noV noW =
  rightTargetWidenFrame terminalization
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {ρ₀ = ρ} {ρ⁺ = ρ} {p = r} {q = q}
    prefix-reflⁱ coherent exclusive wfR runtime
    vV noV mode seal★ t⊑ (⊑cast⊑ᵀ mode seal★ s⊑ V⊑W r)
    (rightTargetWidenFrame terminalization
      {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      {ρ₀ = ρ} {ρ⁺ = ρ} {p = p} {q = r}
      prefix-reflⁱ coherent exclusive wfR
      (runtime-⟨⟩ runtime) vV noV mode seal★ s⊑ V⊑W
      (world-coherent-right-value-terminalᵀ
        {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
        {ρ₀ = ρ} {ρ⁺ = ρ} {p = p}
        prefix-reflⁱ coherent exclusive wfR
        vV noV vW noW V⊑W))
rightTargetPendingIdWidenSequence
    (world-coherent-right-target-pending-sequence-continuation-proofᵀ
      terminalization)
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {ρ = ρ}
    {p = p} {r = r} {q = q}
    vW seal★ s⊑ t⊑ _ _ _ V⊑W
    coherent exclusive wfR runtime vV noV noW =
  rightTargetIdWidenFrame terminalization
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {ρ₀ = ρ} {ρ⁺ = ρ} {p = r} {q = q}
    prefix-reflⁱ coherent exclusive wfR runtime
    vV noV seal★ t⊑ (⊑cast⊑idᵀ seal★ s⊑ V⊑W r)
    (rightTargetIdWidenFrame terminalization
      {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      {ρ₀ = ρ} {ρ⁺ = ρ} {p = p} {q = r}
      prefix-reflⁱ coherent exclusive wfR
      (runtime-⟨⟩ runtime) vV noV seal★ s⊑ V⊑W
      (world-coherent-right-value-terminalᵀ
        {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
        {ρ₀ = ρ} {ρ⁺ = ρ} {p = p}
        prefix-reflⁱ coherent exclusive wfR
        vV noV vW noW V⊑W))

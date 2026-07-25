module
  proof.WorldCoherent.Right.Target.Resume.NuImprecisionWorldCoherentRightTargetPendingSequenceContinuationProof
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

open import proof.DGG.Core.NuPreservation using (runtime-⟨⟩)
open import QuotientedTermImprecision using
  ( prefix-reflⁱ
  ; ⊑cast⊒ᵀ
  ; ⊑cast⊑idᵀ
  ; ⊑cast⊑ᵀ
  )
open import
  proof.WorldCoherent.Right.Target.Terminalization.NuImprecisionWorldCoherentRightTargetCastTerminalizationDef
  using
  ( WorldCoherentRightTargetCastTerminalization
  ; rightTargetIdWidenFrame
  ; rightTargetNarrowFrame
  ; rightTargetWidenFrame
  )
open import
  proof.WorldCoherent.Right.Target.Resume.NuImprecisionWorldCoherentRightTargetPendingSequenceContinuationDef
  using
  ( WorldCoherentRightTargetPendingSequenceContinuation
  ; rightTargetPendingIdWidenSequence
  ; rightTargetPendingNarrowSequence
  ; rightTargetPendingWidenSequence
  )
open import proof.WorldCoherent.Right.Value.Terminal.NuImprecisionWorldCoherentRightValueTerminalLemma using
  (world-coherent-right-value-terminalᵀ)


world-coherent-right-target-pending-sequence-continuation-proofᵀ :
  WorldCoherentRightTargetCastTerminalization →
  WorldCoherentRightTargetPendingSequenceContinuation
rightTargetPendingNarrowSequence
    (world-coherent-right-target-pending-sequence-continuation-proofᵀ
      terminalization)
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {ρ = ρ}
    {p = p} {r = r} {q = q}
    vW mode seal★ s⊒ t⊒
    s-shape s-comp t-shape t-comp _ V⊑W
    coherent exclusive unique wfR runtime vV noV noW =
  rightTargetNarrowFrame terminalization
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {ρ₀ = ρ} {ρ⁺ = ρ} {p = r} {q = q}
    prefix-reflⁱ coherent exclusive unique wfR runtime
    vV noV mode seal★ t⊒ t-shape t-comp
    (⊑cast⊒ᵀ mode seal★ s⊒ V⊑W r s-shape s-comp)
    (rightTargetNarrowFrame terminalization
      {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      {ρ₀ = ρ} {ρ⁺ = ρ} {p = p} {q = r}
      prefix-reflⁱ coherent exclusive unique wfR
      (runtime-⟨⟩ runtime) vV noV mode seal★ s⊒
      s-shape s-comp V⊑W
      (world-coherent-right-value-terminalᵀ
        {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
        {ρ₀ = ρ} {ρ⁺ = ρ} {p = p}
        prefix-reflⁱ coherent exclusive unique wfR
        vV noV vW noW V⊑W))
rightTargetPendingWidenSequence
    (world-coherent-right-target-pending-sequence-continuation-proofᵀ
      terminalization)
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {ρ = ρ}
    {p = p} {r = r} {q = q}
    vW mode seal★ s⊑ t⊑
    s-shape s-comp t-shape t-comp _ V⊑W
    coherent exclusive unique wfR runtime vV noV noW =
  rightTargetWidenFrame terminalization
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {ρ₀ = ρ} {ρ⁺ = ρ} {p = r} {q = q}
    prefix-reflⁱ coherent exclusive unique wfR runtime
    vV noV mode seal★ t⊑ t-shape t-comp
    (⊑cast⊑ᵀ mode seal★ s⊑ V⊑W r s-shape s-comp)
    (rightTargetWidenFrame terminalization
      {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      {ρ₀ = ρ} {ρ⁺ = ρ} {p = p} {q = r}
      prefix-reflⁱ coherent exclusive unique wfR
      (runtime-⟨⟩ runtime) vV noV mode seal★ s⊑
      s-shape s-comp V⊑W
      (world-coherent-right-value-terminalᵀ
        {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
        {ρ₀ = ρ} {ρ⁺ = ρ} {p = p}
        prefix-reflⁱ coherent exclusive unique wfR
        vV noV vW noW V⊑W))
rightTargetPendingIdWidenSequence
    (world-coherent-right-target-pending-sequence-continuation-proofᵀ
      terminalization)
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {ρ = ρ}
    {p = p} {r = r} {q = q}
    vW seal★ s⊑ t⊑
    s-shape s-comp t-shape t-comp _ V⊑W
    coherent exclusive unique wfR runtime vV noV noW =
  rightTargetIdWidenFrame terminalization
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {ρ₀ = ρ} {ρ⁺ = ρ} {p = r} {q = q}
    prefix-reflⁱ coherent exclusive unique wfR runtime
    vV noV seal★ t⊑ t-shape t-comp
    (⊑cast⊑idᵀ seal★ s⊑ V⊑W r s-shape s-comp)
    (rightTargetIdWidenFrame terminalization
      {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      {ρ₀ = ρ} {ρ⁺ = ρ} {p = p} {q = r}
      prefix-reflⁱ coherent exclusive unique wfR
      (runtime-⟨⟩ runtime) vV noV seal★ s⊑
      s-shape s-comp V⊑W
      (world-coherent-right-value-terminalᵀ
        {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
        {ρ₀ = ρ} {ρ⁺ = ρ} {p = p}
        prefix-reflⁱ coherent exclusive unique wfR
        vV noV vW noW V⊑W))

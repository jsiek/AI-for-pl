module
  proof.WorldCoherent.Right.Target.Resume.NuImprecisionWorldCoherentRightTargetPendingNarrowSequenceContextProof
  where

-- File Charter:
--   * Proves the contextual pending target-narrowing sequence continuation
--     from contextual zero-step terminalization and target-narrow framing.
--   * Makes the remaining recursive cycle explicit as a higher-order
--     dependency; canonical assembly still belongs to the private
--     rank-decreasing target-administration SCC.
--   * Contains no result/view/outcome type, postulate, hole, permissive
--     option, termination bypass, compatibility shim, or broad DGG import.

open import Data.Product using (_,_)
open import proof.DGG.Core.NuPreservation using (runtime-⟨⟩)
open import QuotientedTermImprecision using
  (prefix-reflⁱ; ⊑cast⊒ᵀ)
open import
  proof.WorldCoherent.Right.Target.Resume.NuImprecisionWorldCoherentRightTargetPendingNarrowSequenceContextDef
  using (WorldCoherentRightTargetPendingNarrowSequenceContextᵀ)
open import
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetNarrowFrameContextDef
  using (WorldCoherentRightTargetNarrowFrameContextᵀ)
open import
  proof.WorldCoherent.Right.Value.Terminal.NuImprecisionWorldCoherentRightValueTerminalContextDef
  using (WorldCoherentRightValueTerminalContextᵀ)


world-coherent-right-target-pending-narrow-sequence-context-proofᵀ :
  WorldCoherentRightValueTerminalContextᵀ →
  WorldCoherentRightTargetNarrowFrameContextᵀ →
  WorldCoherentRightTargetPendingNarrowSequenceContextᵀ
world-coherent-right-target-pending-narrow-sequence-context-proofᵀ
    terminal narrow
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {ρ = ρ}
    {p = p} {r = r} {q = q}
    vW mode seal★ s⊒ t⊒ _ _ _ V⊑W
    coherent exclusive unique wfR runtime vV noV noW
    with terminal
      {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      {ρ₀ = ρ} {ρ⁺ = ρ} {p = p}
      prefix-reflⁱ coherent exclusive unique wfR
      vV noV vW noW V⊑W
world-coherent-right-target-pending-narrow-sequence-context-proofᵀ
    terminal narrow
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {ρ = ρ}
    {p = p} {r = r} {q = q}
    vW mode seal★ s⊒ t⊒ _ _ _ V⊑W
    coherent exclusive unique wfR runtime vV noV noW
    | seed , seed-context , seed-prefix
    with narrow
      {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      {ρ₀ = ρ} {ρ⁺ = ρ} {p = p} {q = r}
      prefix-reflⁱ coherent exclusive unique wfR
      (runtime-⟨⟩ runtime) vV noV mode seal★ s⊒ V⊑W
      seed seed-context seed-prefix
world-coherent-right-target-pending-narrow-sequence-context-proofᵀ
    terminal narrow
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {ρ = ρ}
    {p = p} {r = r} {q = q}
    vW mode seal★ s⊒ t⊒ _ _ _ V⊑W
    coherent exclusive unique wfR runtime vV noV noW
    | seed , seed-context , seed-prefix
    | first , first-context , first-prefix =
  narrow
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {ρ₀ = ρ} {ρ⁺ = ρ} {p = r} {q = q}
    prefix-reflⁱ coherent exclusive unique wfR runtime
    vV noV mode seal★ t⊒
    (⊑cast⊒ᵀ mode seal★ s⊒ V⊑W r)
    first first-context first-prefix

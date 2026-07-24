module
  proof.WorldCoherent.Right.Target.Resume.NuImprecisionWorldCoherentRightTargetPendingCastPrependContextLemma
  where

-- File Charter:
--   * Exposes canonical contextual target-step prepending beneath an
--     arbitrary pending target-cast list.
--   * Supplies only the canonical context-preserving target-step prepend.
--   * Contains no additional theorem shape, result/view/outcome type,
--     postulate, hole, permissive option, or broad DGG import.

open import
  proof.WorldCoherent.Right.Target.Framing.NuImprecisionWorldCoherentRightTargetKeepPrependContextLemma
  using (world-coherent-right-target-keep-prepend-contextᵀ)
open import
  proof.WorldCoherent.Right.Target.Resume.NuImprecisionWorldCoherentRightTargetPendingCastPrependContextDef
  using (WorldCoherentRightTargetPendingCastPrependContextᵀ)
open import
  proof.WorldCoherent.Right.Target.Resume.NuImprecisionWorldCoherentRightTargetPendingCastPrependContextProof
  using
  (world-coherent-right-target-pending-cast-prepend-context-proofᵀ)


world-coherent-right-target-pending-cast-prepend-contextᵀ :
  WorldCoherentRightTargetPendingCastPrependContextᵀ
world-coherent-right-target-pending-cast-prepend-contextᵀ
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {ρ = ρ}
    {V = V} {M′ = M′} {N′ = N′}
    {A = A} {B = B} {cs = cs} {p = p}
    target→ caught context-eq right-prefix =
  world-coherent-right-target-pending-cast-prepend-context-proofᵀ
    world-coherent-right-target-keep-prepend-contextᵀ
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {ρ = ρ}
    {V = V} {M′ = M′} {N′ = N′}
    {A = A} {B = B} {cs = cs} {p = p}
    target→ caught context-eq right-prefix

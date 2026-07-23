module proof.DGG.TerminalForward.NuDGGTerminalForwardClosedProof where

-- File Charter:
--   * Specializes the strict arbitrary-world forward terminal theorem to the
--     exact closed forward component consumed by DGG.
--   * Keeps this cheap statement-fit check independent of the compiler and
--     public gradual-guarantee spine.
--   * Contains no canonical engine assembly, postulate, hole, or permissive
--     option.

open import proof.DGG.Core.NuDGGClosedWorld using
  (empty-store-wf; empty-world-coherent)
open import proof.DGG.TerminalForward.NuDGGTerminalForwardClosedDef using
  (ClosedForwardSourceValueᵀ)
open import proof.DGG.TerminalForward.NuDGGTerminalForwardDef using
  (WorldCoherentForwardSourceValueᵀ)
open import proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessProof using
  (assumption-membership-unique-empty)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityProof using
  (source-name-exclusive-empty)


world-coherent-forward-source-value-closed-proofᵀ :
  WorldCoherentForwardSourceValueᵀ →
  ClosedForwardSourceValueᵀ
world-coherent-forward-source-value-closed-proofᵀ
  forward okN okN′ N⊑N′ =
  forward empty-world-coherent source-name-exclusive-empty
    assumption-membership-unique-empty empty-store-wf empty-store-wf
    okN okN′ N⊑N′

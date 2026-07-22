module proof.NuDGGTerminalForwardClosedProof where

-- File Charter:
--   * Specializes the strict arbitrary-world forward terminal theorem to the
--     exact closed forward component consumed by DGG.
--   * Keeps this cheap statement-fit check independent of the compiler and
--     public gradual-guarantee spine.
--   * Contains no canonical engine assembly, postulate, hole, or permissive
--     option.

open import proof.NuDGGClosedWorld using
  (empty-store-wf; empty-world-coherent)
open import proof.NuDGGTerminalForwardClosedDef using
  (ClosedForwardSourceValueᵀ)
open import proof.NuDGGTerminalForwardDef using
  (WorldCoherentForwardSourceValueᵀ)
open import proof.NuImprecisionAssumptionMembershipUniquenessProof using
  (assumption-membership-unique-empty)
open import proof.NuImprecisionContextExclusivityProof using
  (source-name-exclusive-empty)


world-coherent-forward-source-value-closed-proofᵀ :
  WorldCoherentForwardSourceValueᵀ →
  ClosedForwardSourceValueᵀ
world-coherent-forward-source-value-closed-proofᵀ
  forward okN okN′ N⊑N′ =
  forward empty-world-coherent source-name-exclusive-empty
    assumption-membership-unique-empty empty-store-wf empty-store-wf
    okN okN′ N⊑N′

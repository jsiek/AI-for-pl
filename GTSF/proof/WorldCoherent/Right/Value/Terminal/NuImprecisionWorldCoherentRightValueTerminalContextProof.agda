module
  proof.WorldCoherent.Right.Value.Terminal.NuImprecisionWorldCoherentRightValueTerminalContextProof
  where

-- File Charter:
--   * Proves the contextual right-value terminal seed from the canonical
--     zero-step terminal theorem.
--   * Supplies reflexivity for both the unchanged context and target-only
--     lineage prefix.
--   * Contains no result/view/outcome hierarchy, postulate, hole, permissive
--     option, termination bypass, or broad simulation import.

open import Agda.Builtin.Equality using (refl)
open import Data.Product using (_,_)

open import proof.Right.StorePrefix.NuImprecisionRightOnlyStorePrefix using
  (right-only-prefix-refl)
open import
  proof.WorldCoherent.Right.Value.Terminal.NuImprecisionWorldCoherentRightValueTerminalContextDef
  using (WorldCoherentRightValueTerminalContextᵀ)
open import proof.WorldCoherent.Right.Value.Terminal.NuImprecisionWorldCoherentRightValueTerminalLemma using
  (world-coherent-right-value-terminalᵀ)


world-coherent-right-value-terminal-context-proofᵀ :
  WorldCoherentRightValueTerminalContextᵀ
world-coherent-right-value-terminal-context-proofᵀ
    prefix coherent exclusive unique wfR
    vV noV vV′ noV′ rel =
  caught , refl , right-only-prefix-refl
  where
  caught =
    world-coherent-right-value-terminalᵀ
      prefix coherent exclusive unique wfR
      vV noV vV′ noV′ rel

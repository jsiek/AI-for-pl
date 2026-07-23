module proof.WorldCoherent.Value.NuImprecisionWorldCoherentValueCatchupProof where

-- File Charter:
--   * Proves the world-coherent target-value catch-up contract from its
--     ambient-prefix induction contract.
--   * Instantiates the prefix worker at the reflexive store-imprecision
--     prefix and leaves the structural recursion behind that dependency.
--   * Imports no catch-up implementation or one-step dispatcher.

open import QuotientedTermImprecision using (prefix-reflⁱ)
open import proof.WorldCoherent.Value.NuImprecisionWorldCoherentValueCatchupDef using
  (WorldCoherentLeftValueCatchupᵀ)
open import proof.WorldCoherent.Value.NuImprecisionWorldCoherentValueCatchupPrefixDef using
  (WorldCoherentLeftValueCatchupPrefixᵀ)


world-coherent-left-value-catchup-proofᵀ :
  WorldCoherentLeftValueCatchupPrefixᵀ →
  WorldCoherentLeftValueCatchupᵀ
world-coherent-left-value-catchup-proofᵀ
    prefix-catchup coherent exclusive wfL okM vV′ noV′ M⊑V′ =
  prefix-catchup
    prefix-reflⁱ coherent exclusive wfL okM vV′ noV′ M⊑V′

module
  proof.WorldCoherent.Value.NuImprecisionWorldCoherentValueCatchupPrefixProof
  where

-- File Charter:
--   * Derives ordinary ambient-prefix target-value catch-up from the stronger
--     runtime-sibling-preserving contract.
--   * Uses `blame ⊑ blame` as an independent dummy sibling and projects the
--     ordinary caught result.
--   * Removes the duplicate recursive ordinary dispatcher, whose allocation
--     and cast-sequence re-entry did not pass fresh termination checking.
--   * Contains no recursive implementation, quotient capability, postulate,
--     hole, permissive option, or termination bypass.

open import Data.Product using (proj₁)
open import ImprecisionWf using (⊑-src-wf; ⊑-tgt-wf)
open import NuTerms using
  (blame; no•-blame; ok-no)
open import QuotientedTermImprecision using (blame⊑ᵀ)
open import TermTyping using (⊢blame)
open import
  proof.WorldCoherent.Value.NuImprecisionWorldCoherentValueCatchupPrefixDef
  using (WorldCoherentLeftValueCatchupPrefixᵀ)
open import
  proof.WorldCoherent.Value.NuImprecisionWorldCoherentValueCatchupRuntimeSiblingPrefixDef
  using (WorldCoherentLeftValueCatchupRuntimeSiblingPrefixᵀ)


world-coherent-left-value-catchup-prefix-proofᵀ :
  WorldCoherentLeftValueCatchupRuntimeSiblingPrefixᵀ →
  WorldCoherentLeftValueCatchupPrefixᵀ
world-coherent-left-value-catchup-prefix-proofᵀ
    sibling-prefix {A = A} {B = B} {p = p}
    prefix coherent exclusive unique wfL okL
    vL′ noL′ relation =
  proj₁
    (sibling-prefix
      {R = blame} {R′ = blame}
      {C = A} {C′ = B} {q = p}
      prefix coherent exclusive unique wfL okL
      vL′ noL′ relation
      no•-blame (ok-no no•-blame)
      (blame⊑ᵀ (⊢blame (⊑-tgt-wf p)))
      (⊢blame (⊑-src-wf p))
      (⊢blame (⊑-tgt-wf p)))

module
  proof.WorldCoherent.Quotient.InstFunTag.NuImprecisionWorldCoherentQuotientInstFunTagCatchupLemma
  where

-- File Charter:
--   * Assembles eager quotient-inst/function-tag catch-up from the existing
--     plain quotient-inst capability.
--   * Supplies the canonical inert source-widening frame lemma to the strict
--     higher-order eager proof.

open import
  proof.WorldCoherent.Quotient.InstCatchup.NuImprecisionWorldCoherentQuotientInstCatchupDef
  using (WorldCoherentQuotientInstCatchupᵀ)
open import
  proof.WorldCoherent.Quotient.InstFunTag.NuImprecisionWorldCoherentQuotientInstFunTagCatchupDef
  using (WorldCoherentQuotientInstFunTagCatchupᵀ)
open import
  proof.WorldCoherent.Quotient.InstFunTag.NuImprecisionWorldCoherentQuotientInstFunTagCatchupProof
  using (world-coherent-quotient-inst-fun-tag-catchup-proofᵀ)
open import
  proof.WorldCoherent.Source.CastCatchup.NuImprecisionWorldCoherentSourceInertWidenFrameLemma
  using (world-coherent-source-inert-widen-frameᵀ)


world-coherent-quotient-inst-fun-tag-catchupᵀ :
  WorldCoherentQuotientInstCatchupᵀ →
  WorldCoherentQuotientInstFunTagCatchupᵀ
world-coherent-quotient-inst-fun-tag-catchupᵀ plain =
  world-coherent-quotient-inst-fun-tag-catchup-proofᵀ
    plain world-coherent-source-inert-widen-frameᵀ

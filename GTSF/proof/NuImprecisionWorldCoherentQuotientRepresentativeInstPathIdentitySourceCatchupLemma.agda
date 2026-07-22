module
  proof.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentitySourceCatchupLemma
  where

-- File Charter:
--   * Assembles non-vacuous source-only identity-path quotient-inst catch-up
--     from the completed ordinary-down adapter and generated-down capability.
--   * Keeps exact source allocation and the general-cast residual explicit.
--   * Contains no semantic leaf implementation or recursive dispatcher.

open import
  proof.NuImprecisionWorldCoherentFinalSourceNuCastCatchupDef
  using (WorldCoherentFinalSourceNuCastCatchupᵀ)
open import
  proof.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentitySourceCatchupDef
  using (WorldCoherentQuotientRepresentativeInstPathIdentitySourceCatchupᵀ)
open import
  proof.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentitySourceCatchupProof
  using
  (world-coherent-quotient-representative-inst-path-identity-source-catchup-proofᵀ)
open import
  proof.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentitySourceGenDownCatchupDef
  using
  (WorldCoherentQuotientRepresentativeInstPathIdentitySourceGenDownCatchupᵀ)
open import
  proof.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentitySourceIdDownCastWidenCatchupDef
  using
  (WorldCoherentQuotientRepresentativeInstPathIdentitySourceIdDownCastWidenCatchupᵀ)
open import
  proof.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentitySourceIdDownCatchupProof
  using
  (world-coherent-quotient-representative-inst-path-identity-source-id-down-catchup-proofᵀ)


world-coherent-quotient-representative-inst-path-identity-source-catchup-lemmaᵀ :
  WorldCoherentFinalSourceNuCastCatchupᵀ →
  WorldCoherentQuotientRepresentativeInstPathIdentitySourceIdDownCastWidenCatchupᵀ →
  WorldCoherentQuotientRepresentativeInstPathIdentitySourceGenDownCatchupᵀ →
  WorldCoherentQuotientRepresentativeInstPathIdentitySourceCatchupᵀ
world-coherent-quotient-representative-inst-path-identity-source-catchup-lemmaᵀ
    final cast-widen gen-down =
  world-coherent-quotient-representative-inst-path-identity-source-catchup-proofᵀ
    (world-coherent-quotient-representative-inst-path-identity-source-id-down-catchup-proofᵀ
      final cast-widen)
    gen-down

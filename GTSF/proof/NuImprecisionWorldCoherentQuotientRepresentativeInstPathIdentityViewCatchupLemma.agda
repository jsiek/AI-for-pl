module
  proof.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentityViewCatchupLemma
  where

-- File Charter:
--   * Assembles the complete identity-path view boundary from its paired and
--     non-vacuous source-only branches.
--   * Exposes the four ordinary/generated-down semantic capabilities plus
--     exact source allocation, providing a checked fit test for the larger
--     path proof. The top assembly constructs the four capabilities from its
--     mutual-SCC interfaces.
--   * Contains no quotient elimination or semantic leaf implementation.

open import
  proof.NuImprecisionWorldCoherentFinalSourceNuCastCatchupDef
  using (WorldCoherentFinalSourceNuCastCatchupᵀ)
open import
  proof.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentityPairedCatchupLemma
  using
  (world-coherent-quotient-representative-inst-path-identity-paired-catchup-lemmaᵀ)
open import
  proof.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentityPairedGenDownCatchupDef
  using
  (WorldCoherentQuotientRepresentativeInstPathIdentityPairedGenDownCatchupᵀ)
open import
  proof.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentityPairedIdDownCastWidenCatchupDef
  using
  (WorldCoherentQuotientRepresentativeInstPathIdentityPairedIdDownCastWidenCatchupᵀ)
open import
  proof.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentitySourceCatchupLemma
  using
  (world-coherent-quotient-representative-inst-path-identity-source-catchup-lemmaᵀ)
open import
  proof.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentitySourceGenDownCatchupDef
  using
  (WorldCoherentQuotientRepresentativeInstPathIdentitySourceGenDownCatchupᵀ)
open import
  proof.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentitySourceIdDownCastWidenCatchupDef
  using
  (WorldCoherentQuotientRepresentativeInstPathIdentitySourceIdDownCastWidenCatchupᵀ)
open import
  proof.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentityViewCatchupDef
  using (WorldCoherentQuotientRepresentativeInstPathIdentityViewCatchupᵀ)
open import
  proof.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentityViewCatchupProof
  using
  (world-coherent-quotient-representative-inst-path-identity-view-catchup-proofᵀ)


world-coherent-quotient-representative-inst-path-identity-view-catchup-lemmaᵀ :
  WorldCoherentFinalSourceNuCastCatchupᵀ →
  WorldCoherentQuotientRepresentativeInstPathIdentityPairedIdDownCastWidenCatchupᵀ →
  WorldCoherentQuotientRepresentativeInstPathIdentityPairedGenDownCatchupᵀ →
  WorldCoherentQuotientRepresentativeInstPathIdentitySourceIdDownCastWidenCatchupᵀ →
  WorldCoherentQuotientRepresentativeInstPathIdentitySourceGenDownCatchupᵀ →
  WorldCoherentQuotientRepresentativeInstPathIdentityViewCatchupᵀ
world-coherent-quotient-representative-inst-path-identity-view-catchup-lemmaᵀ
    final paired-cast paired-gen source-cast source-gen =
  world-coherent-quotient-representative-inst-path-identity-view-catchup-proofᵀ
    (world-coherent-quotient-representative-inst-path-identity-paired-catchup-lemmaᵀ
      final paired-cast paired-gen)
    (world-coherent-quotient-representative-inst-path-identity-source-catchup-lemmaᵀ
      final source-cast source-gen)

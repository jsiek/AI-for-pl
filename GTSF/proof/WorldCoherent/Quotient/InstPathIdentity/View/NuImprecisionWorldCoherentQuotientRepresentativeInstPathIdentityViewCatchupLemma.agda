module
  proof.WorldCoherent.Quotient.InstPathIdentity.View.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentityViewCatchupLemma
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
  proof.WorldCoherent.Final.SourceNu.NuImprecisionWorldCoherentFinalSourceNuCastCatchupDef
  using (WorldCoherentFinalSourceNuCastCatchupᵀ)
open import
  proof.WorldCoherent.Quotient.InstPathIdentity.Paired.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentityPairedCatchupLemma
  using
  (world-coherent-quotient-representative-inst-path-identity-paired-catchup-lemmaᵀ)
open import
  proof.WorldCoherent.Quotient.InstPathIdentity.Paired.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentityPairedGenDownCatchupDef
  using
  (WorldCoherentQuotientRepresentativeInstPathIdentityPairedGenDownCatchupᵀ)
open import
  proof.WorldCoherent.Quotient.InstPathIdentity.Paired.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentityPairedIdDownCastWidenCatchupDef
  using
  (WorldCoherentQuotientRepresentativeInstPathIdentityPairedIdDownCastWidenCatchupᵀ)
open import
  proof.WorldCoherent.Quotient.InstPathIdentity.Source.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentitySourceCatchupLemma
  using
  (world-coherent-quotient-representative-inst-path-identity-source-catchup-lemmaᵀ)
open import
  proof.WorldCoherent.Quotient.InstPathIdentity.Source.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentitySourceGenDownCatchupDef
  using
  (WorldCoherentQuotientRepresentativeInstPathIdentitySourceGenDownCatchupᵀ)
open import
  proof.WorldCoherent.Quotient.InstPathIdentity.Source.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentitySourceIdDownCastWidenCatchupDef
  using
  (WorldCoherentQuotientRepresentativeInstPathIdentitySourceIdDownCastWidenCatchupᵀ)
open import
  proof.WorldCoherent.Quotient.InstPathIdentity.View.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentityViewCatchupDef
  using (WorldCoherentQuotientRepresentativeInstPathIdentityViewCatchupᵀ)
open import
  proof.WorldCoherent.Quotient.InstPathIdentity.View.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentityViewCatchupProof
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

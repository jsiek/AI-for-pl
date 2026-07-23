module
  proof.WorldCoherent.Quotient.InstPathIdentity.Paired.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentityPairedCatchupLemma
  where

-- File Charter:
--   * Assembles paired identity-path quotient-inst catch-up from the completed
--     ordinary-down adapter and the remaining generated-down capability.
--   * Makes the exact source-allocation and general-cast residual dependencies
--     explicit at the larger proof boundary.
--   * Contains no semantic leaf implementation or recursive dispatcher.

open import
  proof.WorldCoherent.Final.SourceNu.NuImprecisionWorldCoherentFinalSourceNuCastCatchupDef
  using (WorldCoherentFinalSourceNuCastCatchupᵀ)
open import
  proof.WorldCoherent.Quotient.InstPathIdentity.Paired.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentityPairedCatchupDef
  using (WorldCoherentQuotientRepresentativeInstPathIdentityPairedCatchupᵀ)
open import
  proof.WorldCoherent.Quotient.InstPathIdentity.Paired.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentityPairedCatchupProof
  using
  (world-coherent-quotient-representative-inst-path-identity-paired-catchup-proofᵀ)
open import
  proof.WorldCoherent.Quotient.InstPathIdentity.Paired.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentityPairedGenDownCatchupDef
  using
  (WorldCoherentQuotientRepresentativeInstPathIdentityPairedGenDownCatchupᵀ)
open import
  proof.WorldCoherent.Quotient.InstPathIdentity.Paired.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentityPairedIdDownCastWidenCatchupDef
  using
  (WorldCoherentQuotientRepresentativeInstPathIdentityPairedIdDownCastWidenCatchupᵀ)
open import
  proof.WorldCoherent.Quotient.InstPathIdentity.Paired.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentityPairedIdDownCatchupProof
  using
  (world-coherent-quotient-representative-inst-path-identity-paired-id-down-catchup-proofᵀ)


world-coherent-quotient-representative-inst-path-identity-paired-catchup-lemmaᵀ :
  WorldCoherentFinalSourceNuCastCatchupᵀ →
  WorldCoherentQuotientRepresentativeInstPathIdentityPairedIdDownCastWidenCatchupᵀ →
  WorldCoherentQuotientRepresentativeInstPathIdentityPairedGenDownCatchupᵀ →
  WorldCoherentQuotientRepresentativeInstPathIdentityPairedCatchupᵀ
world-coherent-quotient-representative-inst-path-identity-paired-catchup-lemmaᵀ
    final cast-widen gen-down =
  world-coherent-quotient-representative-inst-path-identity-paired-catchup-proofᵀ
    (world-coherent-quotient-representative-inst-path-identity-paired-id-down-catchup-proofᵀ
      final cast-widen)
    gen-down

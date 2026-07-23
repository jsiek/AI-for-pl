module proof.WorldCoherent.Quotient.InstCatchup.NuImprecisionWorldCoherentQuotientInstCatchupLemma where

-- File Charter:
--   * Assembles quotient-inst catch-up from exact source allocation, the two
--     permutation-step leaves, and the mutual-SCC capabilities.
--   * Constructs both ordinary-down and both generated-down leaves from
--     value-prefix and terminal quotient catch-up.
--   * Checks the complete path normalization, path case split, representative
--     exposure, and quotient elimination stack without importing leaf proofs.
--   * Contains no semantic leaf implementation or recursive dispatcher.

open import
  proof.WorldCoherent.Final.SourceNu.NuImprecisionWorldCoherentFinalSourceNuCastCatchupDef
  using (WorldCoherentFinalSourceNuCastCatchupᵀ)
open import
  proof.WorldCoherent.Quotient.InstCatchup.NuImprecisionWorldCoherentQuotientInstCatchupDef
  using (WorldCoherentQuotientInstCatchupᵀ)
open import
  proof.WorldCoherent.Quotient.InstCatchup.NuImprecisionWorldCoherentQuotientInstCatchupProof
  using (world-coherent-quotient-inst-catchup-proofᵀ)
open import
  proof.WorldCoherent.Quotient.InstPath.NuImprecisionWorldCoherentQuotientRepresentativeInstPathCatchupDef
  using
  ( WorldCoherentQuotientRepresentativeInstPathCatchupᵀ
  ; path-refl
  ; path-step
  )
open import
  proof.WorldCoherent.Quotient.InstPath.NuImprecisionWorldCoherentQuotientRepresentativeInstPathCatchupProof
  using
  (world-coherent-quotient-representative-inst-path-catchup-proofᵀ)
open import
  proof.WorldCoherent.Quotient.InstPathIdentity.Core.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentityCatchupProof
  using
  (world-coherent-quotient-representative-inst-path-identity-catchup-proofᵀ)
open import
  proof.WorldCoherent.Quotient.InstPathIdentity.Core.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentityCatchupDef
  using (WorldCoherentQuotientRepresentativeInstPathIdentityCatchupᵀ)
open import
  proof.WorldCoherent.Quotient.InstPathIdentity.Paired.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentityPairedGenDownCatchupDef
  using
  (WorldCoherentQuotientRepresentativeInstPathIdentityPairedGenDownCatchupᵀ)
open import
  proof.WorldCoherent.Quotient.InstPathIdentity.Paired.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentityPairedGenDownCatchupProof
  using
  (world-coherent-quotient-representative-inst-path-identity-paired-gen-down-catchup-proofᵀ)
open import
  proof.WorldCoherent.Quotient.InstPathIdentity.Paired.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentityPairedIdDownCastWidenCatchupDef
  using
  (WorldCoherentQuotientRepresentativeInstPathIdentityPairedIdDownCastWidenCatchupᵀ)
open import
  proof.WorldCoherent.Quotient.InstPathIdentity.Paired.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentityPairedIdDownCastWidenCatchupProof
  using
  (world-coherent-quotient-representative-inst-path-identity-paired-id-down-cast-widen-catchup-proofᵀ)
open import
  proof.WorldCoherent.Quotient.InstPathIdentity.Source.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentitySourceGenDownCatchupDef
  using
  (WorldCoherentQuotientRepresentativeInstPathIdentitySourceGenDownCatchupᵀ)
open import
  proof.WorldCoherent.Quotient.InstPathIdentity.Source.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentitySourceGenDownCatchupProof
  using
  (world-coherent-quotient-representative-inst-path-identity-source-gen-down-catchup-proofᵀ)
open import
  proof.WorldCoherent.Quotient.InstPathIdentity.Source.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentitySourceIdDownCastWidenCatchupDef
  using
  (WorldCoherentQuotientRepresentativeInstPathIdentitySourceIdDownCastWidenCatchupᵀ)
open import
  proof.WorldCoherent.Quotient.InstPathIdentity.Source.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentitySourceIdDownCastWidenCatchupProof
  using
  (world-coherent-quotient-representative-inst-path-identity-source-id-down-cast-widen-catchup-proofᵀ)
open import
  proof.WorldCoherent.Quotient.InstPathIdentity.View.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentityViewCatchupLemma
  using
  (world-coherent-quotient-representative-inst-path-identity-view-catchup-lemmaᵀ)
open import
  proof.WorldCoherent.Quotient.InstPath.NuImprecisionWorldCoherentQuotientRepresentativeInstPathSourceStepCatchupDef
  using (WorldCoherentQuotientRepresentativeInstPathSourceStepCatchupᵀ)
open import
  proof.WorldCoherent.Quotient.InstPath.NuImprecisionWorldCoherentQuotientRepresentativeInstPathTargetStepCatchupDef
  using (WorldCoherentQuotientRepresentativeInstPathTargetStepCatchupᵀ)
open import
  proof.WorldCoherent.Quotient.Final.NuImprecisionWorldCoherentQuotientFinalCatchupDef
  using (WorldCoherentQuotientFinalCatchupᵀ)
open import
  proof.WorldCoherent.Value.NuImprecisionWorldCoherentValueCatchupPrefixDef
  using (WorldCoherentLeftValueCatchupPrefixᵀ)


world-coherent-quotient-inst-catchup-lemmaᵀ :
  WorldCoherentFinalSourceNuCastCatchupᵀ →
  WorldCoherentQuotientRepresentativeInstPathSourceStepCatchupᵀ →
  WorldCoherentQuotientRepresentativeInstPathTargetStepCatchupᵀ →
  WorldCoherentLeftValueCatchupPrefixᵀ →
  WorldCoherentQuotientFinalCatchupᵀ →
  WorldCoherentQuotientInstCatchupᵀ
world-coherent-quotient-inst-catchup-lemmaᵀ
    final source-step target-step value-catchup quotient-final =
  world-coherent-quotient-inst-catchup-proofᵀ
    (world-coherent-quotient-representative-inst-path-catchup-proofᵀ
      path-cases)
  where
  paired-cast :
    WorldCoherentQuotientRepresentativeInstPathIdentityPairedIdDownCastWidenCatchupᵀ
  paired-cast =
    world-coherent-quotient-representative-inst-path-identity-paired-id-down-cast-widen-catchup-proofᵀ
      value-catchup quotient-final

  source-cast :
    WorldCoherentQuotientRepresentativeInstPathIdentitySourceIdDownCastWidenCatchupᵀ
  source-cast =
    world-coherent-quotient-representative-inst-path-identity-source-id-down-cast-widen-catchup-proofᵀ
      value-catchup quotient-final

  paired-gen :
    WorldCoherentQuotientRepresentativeInstPathIdentityPairedGenDownCatchupᵀ
  paired-gen =
    world-coherent-quotient-representative-inst-path-identity-paired-gen-down-catchup-proofᵀ
      value-catchup quotient-final

  source-gen :
    WorldCoherentQuotientRepresentativeInstPathIdentitySourceGenDownCatchupᵀ
  source-gen =
    world-coherent-quotient-representative-inst-path-identity-source-gen-down-catchup-proofᵀ
      value-catchup quotient-final

  identity : WorldCoherentQuotientRepresentativeInstPathIdentityCatchupᵀ
  identity =
    world-coherent-quotient-representative-inst-path-identity-catchup-proofᵀ
      (world-coherent-quotient-representative-inst-path-identity-view-catchup-lemmaᵀ
        final paired-cast paired-gen source-cast source-gen)

  path-cases : WorldCoherentQuotientRepresentativeInstPathCatchupᵀ
  path-cases path-refl path-refl
      coherent exclusive wfL okN vVd noVd vV′ noV′
      inert-d′ inert-u′ down widening =
    identity coherent exclusive wfL okN vVd noVd vV′ noV′
      inert-d′ inert-u′ down widening
  path-cases path-refl (path-step step rest)
      coherent exclusive wfL okN vVd noVd vV′ noV′
      inert-d′ inert-u′ down widening =
    target-step {step = step} {rest = rest}
      coherent exclusive wfL okN vVd noVd vV′ noV′
      inert-d′ inert-u′ down widening
  path-cases (path-step step rest) targetPath
      coherent exclusive wfL okN vVd noVd vV′ noV′
      inert-d′ inert-u′ down widening =
    source-step {step = step} {rest = rest} {targetPath = targetPath}
      coherent exclusive wfL okN vVd noVd vV′ noV′
      inert-d′ inert-u′ down widening

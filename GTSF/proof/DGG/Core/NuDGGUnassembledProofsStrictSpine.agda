module proof.DGG.Core.NuDGGUnassembledProofsStrictSpine where

-- File Charter:
--   * Aggregates completed strict higher-order `Proof` modules that have no
--     canonical `Lemma` consumer and no other in-repository importer.
--   * Keeps conditional proof progress on an explicit checked surface while
--     its semantic dependencies are still supplied as theorem parameters.
--   * Includes the completed right/source-`∀` proof aggregate because its
--     conditional proof leaves likewise have no canonical `Lemma` consumer.
--   * Imports no permissive or known-incomplete implementation. The repository
--     audit records candidates excluded after a failed strict Agda check.
--   * Remove an import when the corresponding proof is promoted through a
--     canonical `Lemma`.

import
  proof.Right.SourceAll.ClosingValues.NuImprecisionRightSourceAllStrictSpine
import
  proof.Source.Administration.NuImprecisionSourceAdministrationMeasureProof
import
  proof.WorldCoherent.Final.SourceNu.NuImprecisionWorldCoherentFinalSourceNuCastCatchupProof
import
  proof.WorldCoherent.Final.SourceNu.NuImprecisionWorldCoherentFinalSourceNuCatchupProof
import
  proof.WorldCoherent.Final.SourceNu.NuImprecisionWorldCoherentFinalSourceNuCastIndexBodyViewProof
import
  proof.WorldCoherent.Right.Target.Terminalization.NuImprecisionWorldCoherentRightTargetPendingNuAllocationFromPairedLambdaAccProof
import
  proof.WorldCoherent.Right.Target.Terminalization.NuImprecisionWorldCoherentRightTargetPendingNuAllocationPairedFinalBodyInversionProof
import
  proof.WorldCoherent.Source.CastCatchup.NuImprecisionWorldCoherentSourceBulletCatchupProof
import
  proof.WorldCoherent.Source.NuCatchup.NuImprecisionWorldCoherentSourceNuCatchupProof

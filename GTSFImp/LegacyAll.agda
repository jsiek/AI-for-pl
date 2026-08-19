module LegacyAll where

-- File Charter:
--   * Type-checks the quarantined legacy residualized inversion chain.
--   * This aggregate is intentionally not checked with `--safe`, because
--     it imports the legacy coverage-pragma source-strip workers.
--   * Once the legacy coverage debt is repaired, these modules should move
--     back into `All.agda` and this aggregate should be deleted.

import proof.DGG.Inversion.SourceStripColumnView
import proof.DGG.Inversion.SourceStripWorkerProof
import proof.DGG.Inversion.SourceStripLemma
import proof.DGG.Inversion.TargetWalkProof
import proof.DGG.Inversion.TargetWalkLemma
import proof.DGG.Inversion.RightInjInversion2Proof
import proof.DGG.Inversion.RightInjInversion2Lemma

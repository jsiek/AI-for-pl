module All where

-- File Charter:
--   * Type-checking this module type-checks the whole development.
--   * Import policy: list the TOP-LEVEL modules only — the finished
--     baseline metatheory, the finished major lemmas (their public
--     Lemma/theorem modules), and the current proof frontier. Helper
--     modules (Def/Proof internals, Support files, workers) are
--     checked transitively and are deliberately NOT listed here.
--   * Leaf gates: files that nothing imports (probes, example suites,
--     catalogs, counterexample records, and checked-but-unconsumed
--     libraries) must be listed in the "Leaf gates" section below or
--     they silently leave the gate.
--   * FunExt is listed explicitly to keep the development's single
--     axiom visible.

------------------------------------------------------------------------
-- Axiom base
------------------------------------------------------------------------

import FunExt

------------------------------------------------------------------------
-- Baseline metatheory (finished)
------------------------------------------------------------------------

import proof.TypeSafety.Progress
import proof.TypeSafety.Preservation
import GradualTypeCheck
import proof.ImprecisionConsistency
import proof.Imprecision
import proof.Consistency
import proof.Consistency2
import proof.Reduction

------------------------------------------------------------------------
-- Major lemmas (finished)
------------------------------------------------------------------------

import proof.DGG.CompilePreservesImprecision2
import proof.DGG.Inversion.RightInjInversion2Lemma
import proof.DGG.Inversion.SpineValueProof
import proof.DGG.Parked.ParkedWorldLemma
import proof.DGG.Parked.ParkedD4CheckpointLemma

------------------------------------------------------------------------
-- Current frontier (M4/M5: catch-up lemmas, higher-order)
------------------------------------------------------------------------

import proof.DGG.Catchup.ExtraCastRightProof
import proof.DGG.Catchup.InstCatchupRightProof
import proof.DGG.Catchup.InstCatchupRightRelProof
import proof.DGG.Catchup.InstInversionDef
import proof.DGG.Catchup.InstInversionProof

------------------------------------------------------------------------
-- Current frontier (M6: value catch-up foundation)
------------------------------------------------------------------------

import proof.DGG.Catchup.ValueCatchupRightDef
import proof.DGG.Catchup.ColumnSupportProof
import proof.DGG.Catchup.ExtraCastRightAtProof
import proof.DGG.Catchup.ValueCatchupRightProof
import proof.DGG.Catchup.FuelKnotProof

------------------------------------------------------------------------
-- Leaf gates: nothing imports these; listed so they stay checked
------------------------------------------------------------------------

-- Example suites and catalogs
import Example
import GradualTypeCheckExamples
import ConsistencyExamples
import SourceConsistencyExamples
import proof.DGG.ReachabilityCatalog
import proof.DGG.CompileImageShape
import proof.DGG.Phase3DeepDives
import proof.DGG.GroundCastTargetExamples
import proof.DGG.SmartCommaWitness

-- Probes and counterexample records (design decisions, kept checked)
import proof.DGG.SourceStarProbe
import proof.DGG.CenterCrossingProbe
import proof.DGG.TerminusRebuildProbe
import proof.DGG.StarRepChainProbe
import proof.DGG.SealPeelProbe
import proof.DGG.LambdaImpProbe
import proof.DGG.MovedLinkProbe
import proof.DGG.ChainRideProbe
import proof.DGG.TagBoundaryProbe
import proof.DGG.ExtraCastRight2Counterexample

-- Checked libraries currently without consumers (candidates for M7+)
import proof.DGG.CenterRename
import proof.DGG.WorldSupport
import proof.DGG.TargetExtend
import proof.DGG.TargetBindLift

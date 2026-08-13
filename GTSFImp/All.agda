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
import proof.DGG.Catchup.StructuralValueInstantiationStateDef
import proof.DGG.Catchup.StructuralValueInstantiationCastMassDef
import proof.DGG.Catchup.StructuralValueInstantiationCastMassProof
import proof.DGG.Catchup.StructuralValueInstantiationValueCastMassProof
import proof.DGG.Catchup.StructuralValueInstantiationSpineCastMassProof
import proof.DGG.Catchup.StructuralValueInstantiationPendingCastMassProof
import proof.DGG.Catchup.StructuralValueInstantiationGenCastMassProof
import proof.DGG.Catchup.StructuralValueInstantiationInstCastMassProof
import proof.DGG.Catchup.StructuralValueInstantiationAllCastMassProof
import proof.DGG.Catchup.StructuralFrameOutcomeDef
import proof.DGG.Catchup.StructuralFrameOutcomeProof
import proof.DGG.Catchup.StructuralValueInstantiationReductionProof
import proof.DGG.Catchup.StructuralValueInstantiationViewDef
import proof.DGG.Catchup.StructuralValueInstantiationViewProof
import proof.DGG.Catchup.StructuralValueInstantiationCastProof
import proof.DGG.Catchup.StructuralWorldExtendDef
import proof.DGG.Catchup.StructuralWorldExtendProof
import proof.DGG.Catchup.StructuralWorldRebaseProof
import proof.DGG.Catchup.StructuralWorldTagRebaseDef
import proof.DGG.Catchup.StructuralWorldTagRebaseProof
import proof.DGG.Catchup.StructuralWorldSmartLiftDef
import proof.DGG.Catchup.StructuralWorldSmartLiftProof
import proof.DGG.Catchup.StructuralWorldLiftLeftProof
import proof.DGG.Catchup.StructuralWorldEvidenceProof
import proof.DGG.Catchup.StructuralSourceLambdaReplayProof
import proof.DGG.Catchup.StructuralSourceRebaseReplayProof
import proof.DGG.Catchup.StructuralTargetInstantiationDef
import proof.DGG.Catchup.StructuralTargetInstantiationProof
import proof.DGG.Catchup.StructuralTargetLambdaStepProof
import proof.DGG.Catchup.StructuralTargetGenStepProof
import proof.DGG.Catchup.StructuralTargetInstStepProof
import proof.DGG.Catchup.StructuralTargetConversionStepProof
import proof.DGG.Catchup.StructuralTargetAllStepProof
import proof.DGG.Catchup.StructuralInstantiationDescentDef
import proof.DGG.Catchup.StructuralInstantiationDescentProof

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

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

import proof.DGG.CastTermImprecisionTyping
import proof.DGG.CompilePreservesImprecision
import proof.DGG.GroundingMint
import proof.DGG.GroundingPreserve
import proof.DGG.CastConsistencyViews
import proof.DGG.Inversion.SpineValueLemma
import proof.DGG.Inversion.RightInjInversion2Lemma
import proof.DGG.Parked.ParkedWorldLemma
import proof.DGG.Parked.ParkedD4CheckpointLemma
import proof.DGG.WorldInvariants
import proof.DGG.WorldEvolutionSequence
import proof.DGG.ConversionPivotAlignment
import proof.DGG.CenterRenamePlan
import proof.DGG.TargetExtend

------------------------------------------------------------------------
-- Current frontier (M4/M5: catch-up lemmas, higher-order)
------------------------------------------------------------------------

import proof.DGG.Catchup.InstCatchupRightProof
import proof.DGG.Catchup.InstCatchupRightRelProof
import proof.DGG.Catchup.InstInversionDef
import proof.DGG.Catchup.InstInversionProof
import proof.DGG.Catchup.InstInversionLambdaProof
import proof.DGG.Catchup.StructuralValueInstantiationStateDef
import proof.DGG.Catchup.StructuralValueInstantiationCastMassDef
import proof.DGG.Catchup.StructuralValueInstantiationRankDef
import proof.DGG.Catchup.StructuralValueInstantiationRankProof
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
import proof.DGG.Catchup.StructuralGeneratedFrameGeometryDef
import proof.DGG.Catchup.StructuralTargetFrameAbsorptionDef
import proof.DGG.Catchup.StructuralSpineTypingDef
import proof.DGG.Catchup.StructuralStrictViewSurfaceDef
import proof.DGG.Catchup.StructuralWorldExtendDef
import proof.DGG.Catchup.StructuralWorldExtendProof
import proof.DGG.Catchup.StructuralRightParkedEvolveProof
import proof.DGG.Catchup.BoundaryValueAdaptersProof
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
import proof.DGG.Catchup.StructuralTargetPeelSupportProof
import proof.DGG.Catchup.StructuralTargetSpineStepInversionProof
import proof.DGG.Catchup.StructuralTargetFrameDecompositionProof
import proof.DGG.Catchup.StructuralTargetSourceTransportProof
import proof.DGG.Catchup.StructuralTargetLambdaStepProof
import proof.DGG.Catchup.StructuralTargetGenStepProof
import proof.DGG.Catchup.StructuralTargetInstStepProof
import proof.DGG.Catchup.StructuralTargetInstPeelProof
import proof.DGG.Catchup.StructuralTargetConversionStepProof
import proof.DGG.Catchup.StructuralTargetAllStepProof
import proof.DGG.Catchup.StructuralTargetAllPeelProof
import proof.DGG.Catchup.StructuralTargetLambdaPeelProof
import proof.DGG.Catchup.StructuralTargetGenPeelProof
import proof.DGG.Catchup.StructuralTargetRevealPeelProof
import proof.DGG.Catchup.StructuralTargetConcealPeelProof
import proof.DGG.Catchup.StructuralInstantiationDescentDef
import proof.DGG.Catchup.StructuralInstantiationDescentProof
import proof.DGG.Catchup.StructuralAllDescentProof
import proof.DGG.Catchup.StructuralGenDescentProof
import proof.DGG.Catchup.StructuralInstDescentProof
import proof.DGG.Catchup.StructuralNameInstantiationProof

------------------------------------------------------------------------
-- Current frontier (M6: value catch-up foundation)
------------------------------------------------------------------------

import proof.DGG.Catchup.ValueCatchupRightDef
import proof.DGG.Catchup.FuelSupportProof
import proof.DGG.Catchup.GeneratedProjectionReplacementProof
import proof.DGG.Catchup.TargetCastStepInversionProof
import proof.DGG.Catchup.TagLayerExtractionProof
import proof.DGG.Catchup.ExtraCastRightAtProof
import proof.DGG.Catchup.ValueCatchupRightProof
import proof.DGG.Catchup.StructuralValueKeepProof
import proof.DGG.Catchup.StructuralValueDispatcherProof
import proof.DGG.Catchup.StructuralExtraCastDispatcherProof
import proof.DGG.Catchup.FuelKnotProof
import proof.DGG.Catchup.FuelDischargeProof
import proof.DGG.Catchup.LeftBoundaryCatchupDef
import proof.DGG.Catchup.LeftValueCatchupDef
import proof.DGG.Catchup.LeftValueCatchupLemma
import proof.DGG.Catchup.LeftSourceOperationsDef
import proof.DGG.Catchup.LeftBlameLiftProof
import proof.DGG.Catchup.LeftValueCatchupProof

------------------------------------------------------------------------
-- Current frontier (M8: higher-order DGG assembly)
------------------------------------------------------------------------

import proof.DGG.SimPrimitiveValuesProof
import proof.DGG.SimCastLayerInversion
import proof.DGG.SimSourceCastValuesProof
import proof.DGG.SimPairedCastValuesProof
import proof.DGG.SimConcealRevealPeel
import proof.DGG.SimSourceRevealValuesProof
import proof.DGG.SimPairedRevealValuesProof
import proof.DGG.SimSourceConcealValuesProof
import proof.DGG.SimPairedConcealValuesProof
import proof.DGG.TransportTermImprecisionProof
import proof.DGG.SimProof
import proof.DGG.MultiSimProof
import proof.DGG.MultiSimBackProof
import proof.DGG.TargetBlameCatchupProof
import proof.DGG.SimConcealRevealPeel
import proof.DGG.CatchupToLessPreciseProof
import proof.DGG.DynamicGradualGuaranteeProof

------------------------------------------------------------------------
-- Leaf gates: nothing imports these; listed so they stay checked
------------------------------------------------------------------------

-- Example suites and catalogs
import proof.DGG.WorldSnapshot
import proof.DGG.ImpLadder
import proof.DGG.Examples.Example12
import proof.DGG.Examples.MatchedInstantiation
import proof.DGG.Examples.SourceOnlyInstantiation
import proof.DGG.Examples.PrimitiveBlame
import proof.DGG.Examples.SourceIdentityReveal
import proof.DGG.Examples.TargetIdentityReveal
import proof.DGG.Examples.SourceIdentityConceal
import proof.DGG.Examples.TargetIdentityConceal
import proof.DGG.Example12Worlds
import Example
import GradualTypeCheckExamples
import ConsistencyExamples
import SourceConsistencyExamples
import proof.DGG.ReachabilityCatalog
import proof.DGG.CompileImageShape
import proof.DGG.Phase3DeepDives
import proof.DGG.GroundCastTargetExamples

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
import proof.DGG.notes.probes.TargetExtendPlanExamplesProbe
import proof.DGG.notes.probes.ConversionPivotAlignmentProbe
import proof.DGG.notes.probes.TwoCtxBasicExamplesReductionProbe
import proof.DGG.notes.probes.TwoCtxReductionEvolutionBridgeProbe
import proof.DGG.notes.probes.TwoCtxSimulationResultProbe

-- Checked libraries currently without consumers (candidates for M7+)
import proof.DGG.CenterRename
import proof.DGG.Occupancy
import proof.DGG.WorldSupport
import proof.DGG.TargetBindLift

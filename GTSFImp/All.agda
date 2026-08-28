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
import proof.DGG.TransportTermImprecisionProof
import proof.DGG.TransportTargetTermImprecisionProof
import proof.DGG.GroundingMint
import proof.DGG.GroundingPreserve
import proof.DGG.CastConsistencyViews
import proof.DGG.Inversion.SpineValueLemma
import proof.DGG.Inversion.RightInjInversion2Lemma
import proof.DGG.WorldInvariants
import proof.DGG.WorldEvolutionSequence
import proof.DGG.ConversionPivotAlignment
import proof.DGG.CenterRenamePlan
import proof.DGG.TargetExtend

------------------------------------------------------------------------
-- Current frontier (M6: canonical value catch-up)
------------------------------------------------------------------------

import proof.DGG.Catchup.LeftValueCatchupDef
import proof.DGG.Catchup.LeftValueCatchupLemma
import proof.DGG.Catchup.LeftSourceCastCatchupDef
import proof.DGG.Catchup.LeftSourceTypeAppCatchupDef
import proof.DGG.Catchup.LeftSourceConversionCatchupDef
import proof.DGG.Catchup.LeftPairedConversionCatchupDef
import proof.DGG.Catchup.LeftTargetRevealRebaseCatchupDef
import proof.DGG.Catchup.LeftValueCatchupProof
import proof.DGG.CatchupToMorePreciseProof
import proof.DGG.Catchup.MorePreciseSourceLambdaClosingProof
import proof.DGG.Catchup.MorePreciseGenSafeTargetGroundCastSquareDef
import proof.DGG.Catchup.MorePreciseGenSafeTargetGroundCastSquareLemma
import proof.DGG.Catchup.MorePrecisePairedTargetGroundCastSquareDef
import proof.DGG.Catchup.MorePrecisePairedTargetGroundCastSquareProof
import proof.DGG.Catchup.MorePrecisePairedTargetGroundCastSquareLemma
import proof.DGG.Catchup.MorePreciseTargetCastValueCatchupProof

------------------------------------------------------------------------
-- Current frontier (M8: higher-order DGG assembly)
------------------------------------------------------------------------

import proof.DGG.SimProof
import proof.DGG.TermImprecisionSubstitutionProof
import proof.DGG.SimPairedFunValuesProof
import proof.DGG.SimPairedFunClosingProof
import proof.DGG.SimPairedAllClosingProof
import proof.DGG.SimSourceAllClosingProof
import proof.DGG.SimPairedCastValuesProof
import proof.DGG.SimSourceCastValuesProof
import proof.DGG.SimSourceRevealClosingProof
import proof.DGG.SimPairedRevealClosingProof
import proof.DGG.SimPrimitiveValuesLemma
import proof.DGG.SimPrimitiveClosingProof
import proof.DGG.SimTargetRevealRebaseContextDef
import proof.DGG.MultiSimProof
import proof.DGG.MultiSimBackProof
import proof.DGG.SimBackPairedFunValuesProof
import proof.DGG.SimBackTargetRevealRebaseFunValuesProof
import proof.DGG.SimBackProof
import proof.DGG.TargetBlameCatchupLemma
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
import Example
import GradualTypeCheckExamples
import ConsistencyExamples
import SourceConsistencyExamples
import proof.DGG.GroundCastTargetExamples

-- Probes and counterexample records (design decisions, kept checked)
import proof.DGG.notes.probes.TargetExtendPlanExamplesProbe
import proof.DGG.notes.probes.TwoCtxReductionEvolutionBridgeProbe
import proof.DGG.notes.probes.TwoCtxSimulationResultProbe
import proof.DGG.notes.probes.SourceRebaseBackwardTypeTransportProbe
import proof.DGG.notes.CTIBalanceExample12Ladders

-- Checked libraries currently without consumers (candidates for M7+)
import proof.DGG.Occupancy
import proof.DGG.TransportSourceBindProof
import proof.DGG.TransportTargetBindProof
import proof.DGG.TransportPairedBindProof

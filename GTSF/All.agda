module All where

-- File Charter:
--   * Aggregate checker for the public GTSF metatheory and compiler modules.
--   * Imports the Nu metatheory wrapper so that a single Agda invocation
--     checks the active development plus the compiler path.

import Compile
import CompileTermImprecision
import Types
import ImprecisionWf
import ForallPermutation
import QuotientedTermImprecision
import GradualTypeCheck
import GradualExamples
import Coercions
import Conversion
import NarrowWiden
import GradualTermNarrowing
import GradualTermImprecision
import DynamicGradualGuarantee
import NuTermImprecision
import proof.CastImprecision
import proof.CompileDynamicApplicationTest
import proof.CompileTermImprecision
import proof.EndpointCanonicalMLB
import proof.EndpointCanonicalMLBSimple
import proof.EndpointCanonicalMLBSimpleCompleteness
import proof.EndpointCanonicalMLBSimpleMaximality
import proof.EndpointCanonicalMLBSimpleQuotient
import proof.EndpointCanonicalMLBSimpleSoundness
import proof.EndpointCanonicalMLBSimpleTest
import proof.EndpointCanonicalMLBTest
import proof.MLBGlbExample
import proof.MLBGlbCounterexample
import proof.MLBRouteOperationalExperiment
import proof.ForallPermutationTest
import proof.ForallPermutationProperties
import proof.EndpointCanonicalMLBSimpleRoutes
import proof.EndpointCanonicalMLBSimplePermutation
import proof.EndpointCanonicalMLBSimpleFactor
import proof.EndpointCanonicalMLBSimplePairedSpan
import proof.EndpointCanonicalMLBSimpleFactorization
import proof.EndpointCanonicalMLBSimpleFactorCounterexample
import proof.QuotientedTermImprecisionTest
import proof.NuImprecisionSimulationCore
import proof.NuImprecisionSimulation
import proof.NuImprecisionCatchupScratch
import proof.NuImprecisionCatchupSourceCastTerminal
import proof.NuImprecisionOneStepSourceCastFrames
import proof.NuImprecisionQuotientInstView
import proof.NuImprecisionTargetBlameCatchup
import proof.NuImprecisionAllocationSimulation
import proof.NuReductionDeterminism
import proof.NuDGGTraceAlignment
import proof.NuDGGSpine
import proof.NuDGGStrictSpine
import proof.NuDGGTerminalBackwardBlameAssembly
import proof.NuDGGTerminalBackwardBlameIntegration
import proof.NuDGGTerminalBackwardValueAssembly
import proof.NuDGGTerminalBackwardValueIntegration
import proof.NuDGGTerminalSkeleton
import proof.NuDGGWeakResultPreservation
import proof.MaximalLowerBoundsWf
import StoreCorrespondence
import NuTerms
import TermTyping
import proof.TypePreservation
import TypeCheck
-- Replaced by MediatedNarrowing
-- import TermNarrowingSeparated
import NuExamplesFresh
import NuReduction
import ReductionTrace
import Eval
import Run
import proof.CompileTermNarrowing
import proof.NWTermReduction
-- Replaced by MediatedNarrowing
-- import TermNarrowing
-- import proof.TermNarrowingProperties

-- Replaced by CatchupMediated
-- import proof.CatchupSeparated

import NuMetaTheory

import Mediation
import MediatedNarrowing
import proof.DualRawProperties
import proof.MediationProperties
import proof.MediatedLeftInsertion
import proof.TermRenamingMediated
import proof.TermSubstitutionSyntax
import proof.CatchupMediated
import proof.DGGSourceCastTailMediated
import proof.SimBetaMediated
import proof.DGGBetaMediated
import proof.DGGBetaCastValueCommonMediated
import proof.DGGBetaCastValueMediated
import proof.DGGBetaCastMediated
import proof.DGGStoreChangeMediated
import proof.DGGPrimitiveMediated
import proof.DGGCastMediated
import proof.DynamicGradualGuaranteeMediated
-- The following "Separated" modules need to be ported
-- import proof.LeftNuWideningSeparated
-- import proof.DynamicGradualGuaranteeSeparated
-- Need to port NarrowingExamples to MediatedNarrowing
-- import NarrowingExamples
-- This version of the DGG is obsolete, uses the old TermNarrowing
-- import proof.DynamicGradualGuarantee

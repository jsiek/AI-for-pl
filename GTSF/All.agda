module All where

-- File Charter:
--   * Aggregate checker for the public GTSF metatheory and compiler modules.
--   * Imports the Nu metatheory wrapper so that a single Agda invocation
--     checks the active development plus the compiler path.

import Compile
import Types
import ImprecisionWf
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
import proof.EndpointCanonicalMLB
import proof.EndpointCanonicalMLBProof
import proof.EndpointCanonicalMLBTest
import proof.MLBGlbCounterexample
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

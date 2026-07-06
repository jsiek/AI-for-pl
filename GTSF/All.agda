module All where

-- File Charter:
--   * Aggregate checker for the public GTSF metatheory and compiler modules.
--   * Imports the Nu metatheory wrapper so that a single Agda invocation
--     checks the active development plus the compiler path.

import Compile
import Types
import GradualTypeCheck
import GradualExamples
import Coercions
import NarrowWiden
import GradualTermNarrowing
import StoreCorrespondence
import NuTerms
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

import Mediation
import MediatedNarrowing
import proof.DualRawProperties
import proof.MediationProperties
import proof.MediatedLeftInsertion
import proof.CatchupMediated
import proof.SimBetaMediated
-- The following "Separated" modules need to be ported
import proof.LeftNuWideningSeparated
import proof.DynamicGradualGuaranteeSeparated

import NarrowingExamples
import NuMetaTheory
import proof.DynamicGradualGuarantee

module All where

-- File Charter:
--   * Aggregate checker for the public GTSF metatheory and compiler modules.
--   * Imports the Nu metatheory wrapper so that a single Agda invocation
--     checks the active development plus the compiler path.

import Compile
import Types
import GradualTypeCheck
import GradualTypeCheckExamples
import Coercions
import NarrowWiden
import StoreCorrespondence
import NuTerms
import TypeCheck
import TermNarrowingSeparated
import NuExamplesFresh
import NuReduction
import Eval
import Run
import proof.NWTermReduction
import TermNarrowing
import proof.TermNarrowingProperties
import proof.CatchupSeparated
import Mediation
import MediatedNarrowing
import proof.DualRawProperties
import proof.MediationProperties
import proof.CatchupMediated
import proof.SimBetaMediated
import proof.LeftNuWideningSeparated
import proof.DynamicGradualGuaranteeSeparated
import NarrowingExamples
import NuMetaTheory
import proof.DynamicGradualGuarantee

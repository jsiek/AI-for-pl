module All where

-- File Charter:
--   * Aggregate checker for the public GTSF metatheory and compiler modules.
--   * Imports the Nu metatheory wrapper so that a single Agda invocation
--     checks the active development plus the compiler path.

import Compile
import Types
import Coercions
import NarrowWiden
import NuTerms
import TypeCheck
import NuExamplesFresh
import NuReduction
import TermNarrowing
import NuMetaTheory

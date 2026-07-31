module All where

-- File Charter:
--   Aggregate all of the public files that define GTPLC
--   and theorems about GTPLC.

-- Check this file with agda --safe to catch regressions.

----------------------------------------------------------
-- Definition of GTPLC
----------------------------------------------------------

import Types
import TyStore
import Ctx
import Primitives
import Coercions
import Terms
import Reduction

----------------------------------------------------------
-- Properties of GTPLC
----------------------------------------------------------

import TypeSafety
import TypeNarrow
import NarrowWiden
import ImprecisionTheorems
import EnvironmentNarrowing
import TermNarrowing

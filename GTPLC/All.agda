module All where

-- File Charter:
--   Aggregate all of the public files that define GTPLC
--   and theorems about GTPLC.

-- Check this file with agda to catch regressions.

-- Definition of GTPLC

import Types
import TyStore
import Ctx
import Coercions
import NarrowWiden
import Imprecision
import Terms
import Reduction

-- Properties of GTPLC

import TypeSafety

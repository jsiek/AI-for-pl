module All where

-- File Charter:
--   * Type-checking this module type-checks the whole development.
--   * This branch explores an alternative reduction/typing design; the
--     proof/ directory and everything depending on it (TypeSafety,
--     Eval, Example, GradualTypeCheck, DGG) are removed from the gate
--     and will be re-added as they are rebuilt against the new design.

------------------------------------------------------------------------
-- Core definitions
------------------------------------------------------------------------

import Types
import TyStore
import TermCtx
import Primitives
import Imprecision
import Consistency
import Consistency2
import Conversion
import CastTerms
import Reduction

------------------------------------------------------------------------
-- Alternative shift-free core (exploration)
------------------------------------------------------------------------

import alt.Store
import alt.Conversion
import alt.Terms
import alt.Reduction

------------------------------------------------------------------------
-- Source language and compilation
------------------------------------------------------------------------

import GradualTerms
import GradualTermImprecision
import Compile

------------------------------------------------------------------------
-- Leaf gates: nothing imports these; listed so they stay checked
------------------------------------------------------------------------

import ConsistencyExamples
import alt.probes.EscapeReentryProbe

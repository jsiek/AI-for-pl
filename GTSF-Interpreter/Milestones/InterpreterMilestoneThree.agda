module Milestones.InterpreterMilestoneThree where

-- File Charter:
--   * EXPERIMENTAL after the 2026-08-04 origin merge: O35 must migrate the
--     compiler bridge from the retired term-imprecision API to live QTI.
--   * Focused aggregate for interpreter coercion and source-term narrowing.
--   * Checks intrinsic shape/root alignment, structural closure, compiler
--     image, typed projections, and direct compile monotonicity.
--   * Contains no reduction semantics or reduction-derived theorem.

import Narrowing.InterpreterCoercionNarrowing
import Examples.InterpreterTermAlignmentExamples
import Narrowing.InterpreterTermNarrowing
import Narrowing.CompileInterpreterNarrowing
import proof.InterpreterCoercionNarrowingProof
import SmallStepInterface.InterpreterTermShapeProperties

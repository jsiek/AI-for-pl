module InterpreterMilestoneThree where

-- File Charter:
--   * Focused aggregate for interpreter coercion and source-term narrowing.
--   * Checks structural closure, compiler image, typed projections, and
--     direct compile monotonicity.
--   * Contains no reduction semantics or reduction-derived theorem.

import InterpreterCoercionNarrowing
import InterpreterTermNarrowing
import CompileInterpreterNarrowing
import proof.InterpreterCoercionNarrowingProof
import proof.CompileInterpreterNarrowingApplication
import proof.CompileInterpreterNarrowingPolymorphism
import proof.CompileInterpreterNarrowingPrimitive

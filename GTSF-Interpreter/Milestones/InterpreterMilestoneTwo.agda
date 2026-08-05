module Milestones.InterpreterMilestoneTwo where

-- File Charter:
--   * Focused aggregate for concrete world, environment, and value narrowing.
--   * Checks world extension, alpha-aware type abstraction, joined values,
--     and examples.
--   * Contains no reduction semantics or reduction-derived result.

import Narrowing.InterpreterWorldNarrowing
import Narrowing.InterpreterWorldNarrowingProperties
import Narrowing.InterpreterValueNarrowing
import Narrowing.InterpreterEnvironmentNarrowing
import Narrowing.InterpreterTypeAbstractionNarrowing
import DGG.InterpreterJoined
import Examples.InterpreterValueNarrowingExamples
import Examples.InterpreterTypeAbstractionNarrowingExamples

module InterpreterAll where

-- File Charter:
--   * Aggregate check for the direct interpreter design.
--   * Imports the executable semantics, observations, examples, and four
--     DGG statements in both observation-based and direct-equation forms.
--   * Checks the structural, catch-up-based double-headed interpreter draft.
--   * Checks finite-trace completeness of its single-sided catch-up loops.
--   * Checks reduction-free terminal fuel stability and trace extraction.
--   * Checks proof-relevant world and semantic-value narrowing.
--   * Checks interpreter-source narrowing and direct compiler monotonicity.

import Interpreter
import InterpreterObservations
import InterpreterExamples
import InterpreterDynamicGradualGuarantee
import InterpreterDynamicGradualGuaranteeDirect
import DoubleInterpreter
import DoubleInterpreterCatchUp
import InterpreterMilestoneOne
import InterpreterMilestoneTwo
import InterpreterMilestoneThree

module InterpreterAll where

-- File Charter:
--   * EXPERIMENTAL mixed aggregate for the direct interpreter design.
--   * The active type-soundness surface is
--     `Milestones.InterpreterMilestoneFour`; this
--     larger aggregate includes the O34/O35-blocked DGG draft.
--   * Imports the executable semantics, observations, examples, and four
--     DGG statements in both observation-based and direct-equation forms.
--   * Checks the structural, catch-up-based double-headed interpreter draft.
--   * Checks finite-trace completeness of its single-sided catch-up loops.
--   * Checks reduction-free terminal fuel stability and trace extraction.
--   * Checks proof-relevant world and semantic-value narrowing.
--   * Checks interpreter-source narrowing and direct compiler monotonicity.

import Interpreter
import Core.InterpreterObservations
import Examples.InterpreterExamples
import DGG.InterpreterDynamicGradualGuarantee
import DGG.InterpreterDynamicGradualGuaranteeDirect
import DGG.DoubleInterpreter
import DGG.DoubleInterpreterCatchUp
import Milestones.InterpreterMilestoneOne
import Milestones.InterpreterMilestoneTwo
import Milestones.InterpreterMilestoneThree
import Milestones.InterpreterMilestoneFour
import Milestones.InterpreterMilestoneFiveFoundation

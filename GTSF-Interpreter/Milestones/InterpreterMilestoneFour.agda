module Milestones.InterpreterMilestoneFour where

-- File Charter:
--   * Focused active aggregate for semantic runtime typing, unary interpreter
--     error freedom, and closed-program type soundness.
--   * Checks value closure, allocation, instantiation, application, and
--     coercion without depending on the experimental compiler/DGG bridge.
--   * Compiled-endpoint corollaries remain in
--     `Typing.InterpreterErrorFreedom` but
--     are temporarily outside this aggregate while O35 migrates them to the
--     live quotiented term-imprecision relation.
--   * Contains no reduction semantics or reduction-derived theorem.

import Runtime.InterpreterClosedValue
import Typing.InterpreterSemanticTyping
import Typing.InterpreterTypeSoundness
import proof.InterpreterClosedValueProof
import proof.InterpreterSemanticTypingProperties
import proof.InterpreterCloseValueTyping
import proof.InterpreterCoercionTyping
import proof.InterpreterTypingCore
import proof.InterpreterErrorFreedomCore
import proof.InterpreterTypeSoundnessProof

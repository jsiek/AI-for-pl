module LR-narrow.Context.ClosedValueFuture where

-- File Charter:
--   * Proves persistence of closed interpreter values under unary world growth.
--   * Recurses structurally through captured values and environments.
--   * Contains exactly one exported theorem.

open import LR-narrow.ClosedValues
open import Typing.InterpreterSemanticTypingCore using (WorldExtension)
import proof.InterpreterSemanticTypingProperties as TypingProof

private
  mutual
    closed-value-futureᵖ : ∀ {W U V}
      → WorldExtension W U
      → ClosedValue W V
      → ClosedValue U V
    closed-value-futureᵖ W≤U (closure-closed γ-closed θ-scoped) =
      closure-closed
        (closed-environment-futureᵖ W≤U γ-closed)
        (TypingProof.scope-weaken W≤U θ-scoped)
    closed-value-futureᵖ W≤U constant-closed = constant-closed
    closed-value-futureᵖ W≤U (tagged-closed θ-scoped V-closed) =
      tagged-closed
        (TypingProof.scope-weaken W≤U θ-scoped)
        (closed-value-futureᵖ W≤U V-closed)
    closed-value-futureᵖ W≤U (sealed-closed α-allocated V-closed) =
      sealed-closed
        (TypingProof.allocated-weaken W≤U α-allocated)
        (closed-value-futureᵖ W≤U V-closed)
    closed-value-futureᵖ W≤U
        (function-proxy-closed θ-scoped V-closed) =
      function-proxy-closed
        (TypingProof.scope-weaken W≤U θ-scoped)
        (closed-value-futureᵖ W≤U V-closed)
    closed-value-futureᵖ W≤U (type-abstraction-closed V-closed) =
      type-abstraction-closed (closed-value-futureᵖ W≤U V-closed)
    closed-value-futureᵖ W≤U
        (forall-proxy-closed θ-scoped V-closed) =
      forall-proxy-closed
        (TypingProof.scope-weaken W≤U θ-scoped)
        (closed-value-futureᵖ W≤U V-closed)
    closed-value-futureᵖ W≤U (generalized-closed θ-scoped V-closed) =
      generalized-closed
        (TypingProof.scope-weaken W≤U θ-scoped)
        (closed-value-futureᵖ W≤U V-closed)

    closed-environment-futureᵖ : ∀ {W U γ}
      → WorldExtension W U
      → ClosedEnvironment W γ
      → ClosedEnvironment U γ
    closed-environment-futureᵖ W≤U []-closed = []-closed
    closed-environment-futureᵖ W≤U (V-closed ∷-closed γ-closed) =
      closed-value-futureᵖ W≤U V-closed ∷-closed
        closed-environment-futureᵖ W≤U γ-closed

closed-value-future : ∀ {W U V}
  → WorldExtension W U
  → ClosedValue W V
  → ClosedValue U V
closed-value-future = closed-value-futureᵖ

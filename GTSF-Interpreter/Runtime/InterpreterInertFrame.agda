module Runtime.InterpreterInertFrame where

-- File Charter:
--   * Executes one well-typed inert coercion as an explicit runtime frame.
--   * Returns both the concrete wrapped value and its pointwise interpreter
--     equation.
--   * Applies to arbitrary runtime values, not only closed syntax.
--   * Delegates the structural proof to a private reduction-free module.

open import Coercions using
  (Coercion; Inert; ModeEnv; _∣_∣_⊢_∶_=⇒_)

open import Runtime.InterpreterInertFrameCore public
open import Interpreter using (RuntimeTypeEnvironment)
open import Typing.InterpreterSemanticTypingCore using (RuntimeContext)
open import Types
import proof.InterpreterInertFrameProof as Proof

execute-inert-frame :
  ∀ {W Δ Σ θ μ c A B V}
    (runtime : RuntimeContext W Δ Σ θ)
    (runtime-env : RuntimeTypeEnvironment θ)
    (typing : μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B)
    (inert : Inert c) →
  InertFrameExecution W θ c V inert
execute-inert-frame =
  Proof.execute-inert-frame

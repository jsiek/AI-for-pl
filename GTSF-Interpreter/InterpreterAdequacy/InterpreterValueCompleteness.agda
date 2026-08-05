module InterpreterAdequacy.InterpreterValueCompleteness where

-- File Charter:
--   * Public interface for completeness of value-shaped reified interpreter
--     configurations.
--   * Covers values reached through environment lookup and inert frames, not
--     only raw source terms that are themselves syntactic values.
--   * Delegates the structural proof to the private adequacy layer.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax)

open import Interpreter
open import InterpreterAdequacy.TraceAgreement
open import Typing.InterpreterSemanticTypingCore
open import SmallStepInterface.InterpreterTermShape using (InterpreterTerm)
import InterpreterAdequacy.proof.InterpreterValueCompleteness as Proof
import NuTerms as N

interpret-value-completeᵢ :
  ∀ {W prefix Δ Σ Γ γ θ M P A}
    (world-agreement : WorldTraceAgreement W prefix) →
  RuntimeContext W Δ Σ θ →
  RuntimeTypeEnvironment θ →
  EnvironmentTyping W θ γ Γ →
  (image : InterpreterTerm M) →
  N._∣_∣_⊢_⦂_ Δ Σ Γ M A →
  TermTraceAgreement world-agreement [] γ θ M P →
  N.Value P →
  Σ[ n ∈ StepIndex ]
  Σ[ V ∈ Value ]
    (interpret W γ θ M n ≡ returned W V) ×
    ValueTraceAgreement world-agreement [] V P
interpret-value-completeᵢ =
  Proof.interpret-value-completeᵢ

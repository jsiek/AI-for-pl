module Runtime.InterpreterSyntacticValueTermination where

-- File Charter:
--   * Exposes finite return of successfully closed, typed syntactic values.
--   * The witness is an interpreter index, not a reduction trace.
--   * Delegates the structural direct-interpreter proof to a private module.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Maybe using (just)
open import Data.Product using (Σ-syntax)

open import Interpreter
open import Typing.InterpreterSemanticTypingCore using (RuntimeContext)
import NuTerms as N
import proof.InterpreterSyntacticValueTerminationProof as Proof
open import Types


typed-syntactic-value-eventually-returns :
  ∀ {W Δ Σ Γ γ θ M A U}
    (runtime : RuntimeContext W Δ Σ θ)
    (runtime-env : RuntimeTypeEnvironment θ)
    (vM : N.Value M) →
  N._∣_∣_⊢_⦂_ Δ Σ Γ M A →
  closeValue vM γ θ ≡ just U →
  Σ[ n ∈ StepIndex ] interpret W γ θ M n ≡ returned W U
typed-syntactic-value-eventually-returns =
  Proof.typed-syntactic-value-eventually-returns

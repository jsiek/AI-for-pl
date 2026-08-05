module InterpreterAdequacy.proof.SmallStepBlameCompleteness where

-- File Charter:
--   * Proves blame completeness for closed, typed interpreter source terms.
--   * Instantiates the well-founded blame driver at the empty runtime state.
--   * Keeps the mutually recursive blame-problem infrastructure private.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([])
open import Data.Nat using (zero)
open import Data.Product using (Σ-syntax)

open import Interpreter using
  (StepIndex; World; blamed; run; runtime-type-empty)
open import InterpreterAdequacy.proof.EventualBlameDriver using
  (eventual-blame)
open import InterpreterAdequacy.proof.EventualBlameProblem using
  (interpret-problem)
open import InterpreterAdequacy.proof.InitialTraceAgreement using
  (initial-term-trace-agreement)
open import InterpreterAdequacy.proof.TraceAgreementProperties using
  (empty-world-trace-agreement)
open import Typing.InterpreterSemanticTypingCore using
  (empty-world-typed; environment-empty)
open import SmallStepInterface.InterpreterTermShape using (InterpreterTerm)
open import NuReduction using (_—↠[_]_)
import NuTerms as N
open import proof.InterpreterErrorFreedomCore using
  (empty-runtime-context)

small-step-blame-completeᵢ :
  ∀ {M A changes} →
  (image : InterpreterTerm M) →
  N._∣_∣_⊢_⦂_ zero [] [] M A →
  M —↠[ changes ] N.blame →
  Σ[ n ∈ StepIndex ] Σ[ W ∈ World ] run M n ≡ blamed W
small-step-blame-completeᵢ image M⊢ trace =
  eventual-blame
    (interpret-problem refl empty-world-trace-agreement
      empty-world-typed empty-runtime-context runtime-type-empty
      environment-empty image M⊢ (initial-term-trace-agreement M⊢)
      trace)

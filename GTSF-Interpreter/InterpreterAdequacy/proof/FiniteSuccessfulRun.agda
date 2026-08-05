module InterpreterAdequacy.proof.FiniteSuccessfulRun where

-- File Charter:
--   * Constructs finite fuel, world, and value witnesses for a closed typed
--     interpreter term with a nonempty terminating small-step trace.
--   * Instantiates the well-founded return driver at the empty runtime state.
--   * Contains the private proof of the public finite-success theorem.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_)
open import Data.Nat using (zero)
open import Data.Product using (_,_; Σ-syntax)

open import Interpreter using
  (StepIndex; Value; World; emptyWorld; returned; run;
   runtime-type-empty)
open import InterpreterAdequacy.proof.EventualReturnDriver using
  (eventual-return)
open import InterpreterAdequacy.proof.EventualReturnProblem using
  (ReturnProblem; Successful; interpret-problem)
open import InterpreterAdequacy.proof.InitialTraceAgreement using
  (initial-term-trace-agreement)
open import InterpreterAdequacy.proof.TraceAgreementProperties using
  (empty-world-trace-agreement)
open import Typing.InterpreterSemanticTypingCore using
  (empty-world-typed; environment-empty)
open import SmallStepInterface.InterpreterTermShape using (InterpreterTerm)
open import NuReduction using (StoreChange; StoreChanges; _—↠[_]_)
import NuTerms as N
open import proof.InterpreterErrorFreedomCore using
  (empty-runtime-context)

finite-successful-run-from-nonempty-traceᵢ :
  ∀ {M A change changes v} →
  (image : InterpreterTerm M) →
  N._∣_∣_⊢_⦂_ zero [] [] M A →
  M —↠[ change ∷ changes ] v →
  N.Value v →
  Σ[ n ∈ StepIndex ]
  Σ[ W ∈ World ]
  Σ[ V ∈ Value ] run M n ≡ returned W V
finite-successful-run-from-nonempty-traceᵢ image M⊢ trace vV =
  eventual-return
    (interpret-problem refl empty-world-trace-agreement
      empty-world-typed empty-runtime-context runtime-type-empty
      environment-empty image M⊢ (initial-term-trace-agreement M⊢)
      trace vV)

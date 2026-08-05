module InterpreterAdequacy.FiniteSuccessfulRun where

-- File Charter:
--   * Exposes the constructive finite-success theorem for nonempty terminating
--     traces of closed, typed interpreter source terms.
--   * States the public theorem directly and delegates only its proof body.
--   * Does not expose the mutually recursive return-problem infrastructure.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using ([]; _∷_)
open import Data.Nat using (zero)
open import Data.Product using (Σ-syntax)

open import Interpreter using
  (StepIndex; Value; World; returned; run)
import InterpreterAdequacy.proof.FiniteSuccessfulRun as Proof
open import SmallStepInterface.InterpreterTermShape using (InterpreterTerm)
open import NuReduction using (_—↠[_]_)
import NuTerms as N

finite-successful-run-from-nonempty-traceᵢ :
  ∀ {M A change changes v} →
  (image : InterpreterTerm M) →
  N._∣_∣_⊢_⦂_ zero [] [] M A →
  M —↠[ change ∷ changes ] v →
  N.Value v →
  Σ[ n ∈ StepIndex ]
  Σ[ W ∈ World ]
  Σ[ V ∈ Value ] run M n ≡ returned W V
finite-successful-run-from-nonempty-traceᵢ =
  Proof.finite-successful-run-from-nonempty-traceᵢ

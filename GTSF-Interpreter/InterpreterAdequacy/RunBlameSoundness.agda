module InterpreterAdequacy.RunBlameSoundness where

-- File Charter:
--   * States blame soundness for closed, well-typed programs run by the
--     direct fuel-indexed interpreter.
--   * Produces the exact official small-step store trace to `blame`.
--   * Exposes only the closed-program theorem; recursive simulation remains
--     in `proof/RunBlameSoundnessProof`.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using ([])
open import Data.Nat using (zero)
open import Data.Product using (Σ-syntax; _,_)

open import Interpreter using (blamed; run)
open import InterpreterAdequacy.TraceAgreement
open import InterpreterAdequacy.proof.BlameTrace
open import InterpreterAdequacy.proof.InitialTraceAgreement using
  (initial-term-trace-agreement)
open import InterpreterAdequacy.proof.InterpreterTermNoBullet using
  (interpreter-term-no-bullet)
open import InterpreterAdequacy.proof.RunBlameSoundnessProof using
  (interpret-blame-soundᵢ)
open import InterpreterAdequacy.proof.TraceAgreementProperties using
  (empty-world-trace-agreement; world-trace-agreement-++)
open import SmallStepInterface.InterpreterTermShape using (InterpreterTerm)
open import NuReduction using (StoreChanges; _—↠[_]_)
import NuTerms as N

run-blame-soundᵢ :
  ∀ n {M A W} →
  InterpreterTerm M →
  N._∣_∣_⊢_⦂_ zero [] [] M A →
  run M n ≡ blamed W →
  Σ[ χs ∈ StoreChanges ]
  Σ[ world-agreement ∈ WorldTraceAgreement W χs ]
    (M —↠[ χs ] N.blame)
run-blame-soundᵢ n image M⊢ result-eq
    with interpret-blame-soundᵢ n
      empty-world-trace-agreement
      (interpreter-term-no-bullet image)
      (initial-term-trace-agreement M⊢)
      result-eq
run-blame-soundᵢ n image M⊢ result-eq
    | blame-trace χs path reduction =
  χs , world-trace-agreement-++ empty-world-trace-agreement path ,
    reduction

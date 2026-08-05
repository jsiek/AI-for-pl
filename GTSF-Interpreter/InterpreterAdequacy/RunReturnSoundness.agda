module InterpreterAdequacy.RunReturnSoundness where

-- File Charter:
--   * States successful-return soundness for closed, well-typed programs run
--     by the direct fuel-indexed interpreter.
--   * Produces the exact small-step store-change trace, its final syntactic
--     value, and the agreement with the returned semantic value.
--   * Exposes only the closed-program theorem; recursive simulation remains
--     in `proof/RunReturnSoundnessProof`.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using ([])
open import Data.Nat using (zero)
open import Data.Product using (_×_; Σ-syntax; _,_)

open import Interpreter using (Value; World; returned; run)
open import InterpreterAdequacy.TraceAgreement
open import InterpreterAdequacy.proof.InitialTraceAgreement using
  (initial-term-trace-agreement)
open import InterpreterAdequacy.proof.InterpreterTermNoBullet using
  (interpreter-term-no-bullet)
open import InterpreterAdequacy.proof.ReturnTrace
open import InterpreterAdequacy.proof.RunReturnSoundnessProof using
  (interpret-return-soundᵢ)
open import InterpreterAdequacy.proof.TraceAgreementProperties using
  ( empty-world-trace-agreement
  ; value-trace-value
  ; world-trace-agreement-++
  )
open import SmallStepInterface.InterpreterTermShape using (InterpreterTerm)
open import NuReduction using (StoreChanges; _—↠[_]_)
import NuTerms as N

run-return-soundᵢ :
  ∀ n {M A W V} →
  InterpreterTerm M →
  N._∣_∣_⊢_⦂_ zero [] [] M A →
  run M n ≡ returned W V →
  Σ[ χs ∈ StoreChanges ]
  Σ[ v ∈ N.Term ]
  Σ[ world-agreement ∈ WorldTraceAgreement W χs ]
    (M —↠[ χs ] v) ×
    N.Value v ×
    ValueTraceAgreement world-agreement [] V v
run-return-soundᵢ n image M⊢ result-eq
    with interpret-return-soundᵢ n
      empty-world-trace-agreement
      (interpreter-term-no-bullet image)
      (initial-term-trace-agreement M⊢)
      result-eq
run-return-soundᵢ n image M⊢ result-eq
    | return-trace χs v path reduction V-agrees =
  χs , v , world-trace-agreement-++ empty-world-trace-agreement path ,
    reduction , value-trace-value V-agrees , V-agrees

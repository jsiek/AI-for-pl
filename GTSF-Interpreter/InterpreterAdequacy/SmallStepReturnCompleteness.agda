module InterpreterAdequacy.SmallStepReturnCompleteness where

-- File Charter:
--   * States the public small-step-to-interpreter return-completeness results.
--   * Exposes the complete theorem for every finite trace to a value, together
--     with its reflexive and alignment components.
--   * Keeps the well-founded interpreter simulation in the private proof layer.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using ([])
open import Data.Nat using (zero)
open import Data.Product using (_×_; _,_; Σ-syntax)

open import Interpreter using
  ( StepIndex
  ; Value
  ; World
  ; emptyWorld
  ; returned
  ; run
  )
open import InterpreterAdequacy.BulletCatchUp using (BulletCatchUp)
open import InterpreterAdequacy.FiniteSuccessfulRun using
  (finite-successful-run-from-nonempty-traceᵢ)
open import InterpreterAdequacy.TraceAgreement
import InterpreterAdequacy.proof.BulletCatchUpCompleteness as BulletProof
import InterpreterAdequacy.proof.ReturnCompletenessAlignment as Alignment
import InterpreterAdequacy.proof.SmallStepReturnCompletenessBase as Base
open import InterpreterAdequacy.proof.TraceAgreementProperties using
  (empty-world-trace-agreement)
open import SmallStepInterface.InterpreterTermShape using (InterpreterTerm)
open import NuReduction using (↠-refl; ↠-step; _—↠[_]_)
import NuTerms as N
open import Types using (`∀)

-- Administrative alignment after allocation
------------------------------------------------------------------------

bullet-catch-up-complete :
  ∀ {Δ Σ V A} →
  (vV : N.Value V) →
  (V-ok : InterpreterTerm V) →
  N._∣_∣_⊢_⦂_ Δ Σ [] V (`∀ A) →
  Σ[ R ∈ N.Term ] BulletCatchUp (V N.•) R
bullet-catch-up-complete =
  BulletProof.bullet-catch-up-complete

-- Reflexive completeness
------------------------------------------------------------------------

-- This is the terminal case of the eventual trace induction: the small-step
-- endpoint is already a source value, so no operational alignment is needed.
small-step-return-complete-reflᵢ :
  ∀ {M A} →
  (image : InterpreterTerm M) →
  (vM : N.Value M) →
  (M⊢ : N._∣_∣_⊢_⦂_ zero [] [] M A) →
  Σ[ n ∈ StepIndex ]
  Σ[ V ∈ Value ]
    (run M n ≡ returned emptyWorld V) ×
    ValueTraceAgreement empty-world-trace-agreement [] V M
small-step-return-complete-reflᵢ =
  Base.small-step-return-complete-reflᵢ

-- This version has the same trace-indexed conclusion as the eventual full
-- theorem.  An official value cannot take a leading small step, so its input
-- trace is necessarily reflexive.
small-step-return-complete-valueᵢ :
  ∀ {M A χs v} →
  (image : InterpreterTerm M) →
  (vM : N.Value M) →
  (M⊢ : N._∣_∣_⊢_⦂_ zero [] [] M A) →
  M —↠[ χs ] v →
  N.Value v →
  Σ[ n ∈ StepIndex ]
  Σ[ V ∈ Value ]
  Σ[ world-agreement ∈ WorldTraceAgreement emptyWorld χs ]
    (run M n ≡ returned emptyWorld V) ×
    ValueTraceAgreement world-agreement [] V v
small-step-return-complete-valueᵢ =
  Base.small-step-return-complete-valueᵢ

-- Exact-trace alignment after eventual return
------------------------------------------------------------------------

-- The recursive driver only needs to establish the premise in the middle:
-- some finite interpreter index returns.  Return soundness and deterministic
-- small-step evaluation then recover the exact supplied trace and endpoint.
small-step-return-complete-from-runᵢ :
  ∀ {M A χs v} →
  (image : InterpreterTerm M) →
  (M⊢ : N._∣_∣_⊢_⦂_ zero [] [] M A) →
  (M↠v : M —↠[ χs ] v) →
  (vV : N.Value v) →
  (Σ[ n ∈ StepIndex ]
   Σ[ W ∈ World ]
   Σ[ V ∈ Value ] run M n ≡ returned W V) →
  Σ[ n ∈ StepIndex ]
  Σ[ W ∈ World ]
  Σ[ V ∈ Value ]
  Σ[ world-agreement ∈ WorldTraceAgreement W χs ]
    (run M n ≡ returned W V) ×
    ValueTraceAgreement world-agreement [] V v
small-step-return-complete-from-runᵢ =
  Alignment.small-step-return-complete-from-runᵢ

-- Complete finite-trace return adequacy
------------------------------------------------------------------------

small-step-return-completeᵢ :
  ∀ {M A χs v} →
  (image : InterpreterTerm M) →
  (M⊢ : N._∣_∣_⊢_⦂_ zero [] [] M A) →
  M —↠[ χs ] v →
  N.Value v →
  Σ[ n ∈ StepIndex ]
  Σ[ W ∈ World ]
  Σ[ V ∈ Value ]
  Σ[ world-agreement ∈ WorldTraceAgreement W χs ]
    (run M n ≡ returned W V) ×
    ValueTraceAgreement world-agreement [] V v
small-step-return-completeᵢ image M⊢ ↠-refl vM
    with small-step-return-complete-reflᵢ image vM M⊢
small-step-return-completeᵢ image M⊢ ↠-refl vM
    | n , V , result-eq , V-agrees =
  n , emptyWorld , V , empty-world-trace-agreement ,
    result-eq , V-agrees
small-step-return-completeᵢ image M⊢
    trace@(↠-step root tail) vV =
  small-step-return-complete-from-runᵢ image M⊢ trace vV
    (finite-successful-run-from-nonempty-traceᵢ image M⊢ trace vV)

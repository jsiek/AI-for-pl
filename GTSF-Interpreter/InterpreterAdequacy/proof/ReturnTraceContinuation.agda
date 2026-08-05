module InterpreterAdequacy.proof.ReturnTraceContinuation where

-- File Charter:
--   * Provides generic continuation combinators for successful return traces.
--   * Lifts an already simulated computation through a coercion frame and
--     prepends individual pure administrative steps.
--   * Contains no interpreter recursion and is independent of term typing.

open import Data.List using ([]; _∷_; _++_)

open import Coercions using (Coercion)
open import Interpreter using (Value; World)
open import InterpreterAdequacy.TraceAgreement
open import InterpreterAdequacy.proof.ReturnTrace
open import InterpreterAdequacy.proof.TraceAgreementPath using
  (value-trace-rebase)
open import InterpreterAdequacy.proof.TraceAgreementProperties using
  (world-trace-agreement-++; world-trace-path-++)
open import NuReduction using
  (keep; pure-step; _—→_; _—↠[_]_; ↠-step)
import NuTerms as N
open import proof.Core.Properties.ReductionProperties using
  (applyCoercions; cast-↠; ↠-trans)

prepend-pure-step :
  ∀ {W U prefix P Q V}
    {world-agreement : WorldTraceAgreement W prefix} →
  P —→ Q →
  ReturnTrace world-agreement Q U V →
  ReturnTrace world-agreement P U V
prepend-pure-step step
    (return-trace changes r path reduction V-agrees) =
  return-trace (keep ∷ changes) r
    (world-trace-keep path)
    (↠-step (pure-step step) reduction)
    (value-trace-rebase V-agrees)

continue-under-cast :
  ∀ {W U Z prefix χP P v c R}
    (world-agreement : WorldTraceAgreement W prefix)
    (path-P : WorldTracePath W χP U) →
  P —↠[ χP ] v →
  ReturnTrace
    (world-trace-agreement-++ world-agreement path-P)
    (v N.⟨ applyCoercions χP c ⟩) Z R →
  ReturnTrace world-agreement (P N.⟨ c ⟩) Z R
continue-under-cast world-agreement path-P P-reduction
    (return-trace χC z path-C C-reduction R-agrees) =
  return-trace (_ ++ χC) z
    (world-trace-path-++ path-P path-C)
    (↠-trans (cast-↠ P-reduction) C-reduction)
    (value-trace-rebase R-agrees)

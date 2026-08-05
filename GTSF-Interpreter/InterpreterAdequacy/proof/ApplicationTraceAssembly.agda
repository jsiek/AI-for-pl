module InterpreterAdequacy.proof.ApplicationTraceAssembly where

-- File Charter:
--   * Assembles left evaluation, right evaluation, and semantic application
--     into one small-step return trace.
--   * Accounts explicitly for allocations in the right operand shifting the
--     already evaluated function value.
--   * Contains no interpreter recursion.

open import Data.List using ([]; _++_)

open import Interpreter using (Value; World)
open import InterpreterAdequacy.TraceAgreement
open import InterpreterAdequacy.proof.ReturnTrace
open import InterpreterAdequacy.proof.TraceAgreementPath using
  (value-trace-rebase)
open import InterpreterAdequacy.proof.TraceAgreementProperties using
  ( value-trace-no-bullet
  ; value-trace-value
  ; world-trace-agreement-++
  ; world-trace-path-++
  )
open import NuReduction using
  (StoreChanges; applyTerms; _—↠[_]_)
import NuTerms as N
open import proof.Core.Properties.ReductionProperties using
  (↠-trans; ·₁-↠; ·₂-↠)

assemble-application-return :
  ∀ {W W₁ W₂ Z prefix χL χM χA PL PM v u z V R}
    (world-agreement : WorldTraceAgreement W prefix)
    (path-L : WorldTracePath W χL W₁)
    (path-M : WorldTracePath W₁ χM W₂)
    (path-A : WorldTracePath W₂ χA Z) →
  N.No• PM →
  PL —↠[ χL ] v →
  ValueTraceAgreement
    (world-trace-agreement-++ world-agreement path-L) [] V v →
  applyTerms χL PM —↠[ χM ] u →
  (applyTerms χM v N.· u) —↠[ χA ] z →
  ValueTraceAgreement
    (world-trace-agreement-++
      (world-trace-agreement-++
        (world-trace-agreement-++ world-agreement path-L) path-M)
      path-A)
    [] R z →
  ReturnTrace world-agreement (PL N.· PM) Z R
assemble-application-return
    {χL = χL} {χM = χM} {χA = χA}
    world-agreement path-L path-M path-A
    no-PM L-reduction V-agrees M-reduction A-reduction R-agrees =
  return-trace (χL ++ (χM ++ χA)) _
    combined-path combined-reduction
    (value-trace-rebase R-agrees)
  where
  combined-path =
    world-trace-path-++ path-L (world-trace-path-++ path-M path-A)

  combined-reduction =
    ↠-trans (·₁-↠ no-PM L-reduction)
      (↠-trans
        (·₂-↠ (value-trace-value V-agrees)
          (value-trace-no-bullet V-agrees) M-reduction)
        A-reduction)

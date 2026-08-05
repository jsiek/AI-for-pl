module InterpreterAdequacy.proof.ReturnTrace where

-- File Charter:
--   * Packages the reusable result of a successful interpreter simulation.
--   * Connects an initial reified term to a final semantic value by the exact
--     small-step store trace and a final value trace agreement.
--   * Provides trace assembly and transport across equal returned outcomes;
--     interpreter recursion lives elsewhere.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using ([]; _++_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import Interpreter using (Name; Outcome; Value; World; returned)
open import InterpreterAdequacy.TraceAgreement
open import InterpreterAdequacy.proof.TraceAgreementPath using
  (value-trace-rebase)
open import InterpreterAdequacy.proof.TraceAgreementProperties using
  (world-trace-agreement-++; world-trace-path-++)
open import NuReduction using
  (StoreChanges; _—↠[_]_; ↠-refl)
import NuTerms as N
open import proof.Core.Properties.ReductionProperties using (↠-trans)

record ReturnTrace
    {W χs}
    (world-agreement : WorldTraceAgreement W χs)
    (P : N.Term)
    (U : World)
    (V : Value) : Set₁ where
  constructor return-trace
  field
    changes : StoreChanges
    syntactic-value : N.Term
    world-path : WorldTracePath W changes U
    reduction-trace : P —↠[ changes ] syntactic-value
    value-agreement :
      ValueTraceAgreement
        (world-trace-agreement-++ world-agreement world-path)
        [] V syntactic-value

open ReturnTrace public

return-trace-start-eq :
  ∀ {W U χs}
    {world-agreement : WorldTraceAgreement W χs}
    {P Q V} →
  P ≡ Q →
  ReturnTrace world-agreement Q U V →
  ReturnTrace world-agreement P U V
return-trace-start-eq term-eq
    (return-trace changes v path reduction V-agrees) =
  return-trace changes v path
    (subst (λ P′ → P′ —↠[ changes ] v) (sym term-eq) reduction)
    V-agrees

return-trace-result-eq :
  ∀ {W U Z χs}
    {world-agreement : WorldTraceAgreement W χs}
    {P V R} →
  _≡_ {A = Outcome} (returned U V) (returned Z R) →
  ReturnTrace world-agreement P U V →
  ReturnTrace world-agreement P Z R
return-trace-result-eq Relation.Binary.PropositionalEquality.refl trace =
  trace

return-trace-refl :
  ∀ {W χs}
    {world-agreement : WorldTraceAgreement W χs}
    {P V v} →
  P ≡ v →
  ValueTraceAgreement world-agreement [] V v →
  ReturnTrace world-agreement P W V
return-trace-refl term-eq V-agrees =
  return-trace [] _ world-trace-done
    (subst (λ P′ → P′ —↠[ [] ] _)
      (Relation.Binary.PropositionalEquality.sym term-eq) ↠-refl)
    (value-trace-rebase V-agrees)

compose-return-prefix :
  ∀ {W U Z χs χs′ χs″ P Q R}
    {world-agreement : WorldTraceAgreement W χs} →
  (W⇒U : WorldTracePath W χs′ U) →
  (U⇒Z : WorldTracePath U χs″ Z) →
  P —↠[ χs′ ] Q →
  Q —↠[ χs″ ] R →
  P —↠[ χs′ ++ χs″ ] R
compose-return-prefix W⇒U U⇒Z P⇒Q Q⇒R =
  ↠-trans P⇒Q Q⇒R

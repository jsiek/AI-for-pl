module InterpreterAdequacy.proof.ClosureApplicationSoundness where

-- File Charter:
--   * Assembles closure application soundness once the recursive body
--     interpretation has produced its return trace.
--   * Uses `beta-reification` to join the small-step beta endpoint with the
--     interpreter environment extended by the argument.
--   * Contains no interpreter recursion.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import Interpreter using (Value; World)
open import InterpreterAdequacy.TraceAgreement
open import InterpreterAdequacy.proof.BetaReification using
  (beta-reification)
open import InterpreterAdequacy.proof.ReturnTrace
open import InterpreterAdequacy.proof.SyntaxReification using
  (reified-term)
open import InterpreterAdequacy.proof.TraceAgreementPath using
  (value-trace-rebase)
open import InterpreterAdequacy.proof.TraceAgreementProperties using
  (value-trace-value)
open import NuReduction using
  (keep; pure-step; β; ↠-step; _—↠[_]_)
import NuTerms as N

closure-application-from-body :
  ∀ {W Z χs}
    {world-agreement : WorldTraceAgreement W χs}
    {M body τ vs U u R} →
  body ≡
    N.substˣᵐ (N.extˢˣ (environmentSubstitution vs))
      (N.renameᵗᵐ τ M) →
  ValueTraceAgreement world-agreement [] U u →
  ReturnTrace world-agreement (reified-term τ (u ∷ vs) M) Z R →
  ReturnTrace world-agreement ((N.ƛ body) N.· u) Z R
closure-application-from-body
    {M = M} {body = body} {τ = τ} {vs = vs} {u = u}
    reification U-agrees
    (return-trace changes v path body-reduction R-agrees) =
  return-trace (keep ∷ changes) v
    (world-trace-keep path)
    (↠-step (pure-step (β (value-trace-value U-agrees)))
      (subst
        (λ Q → Q —↠[ changes ] v)
        (sym (beta-reification {M = M} {M′ = body} τ vs u reification))
        body-reduction))
    (value-trace-rebase R-agrees)

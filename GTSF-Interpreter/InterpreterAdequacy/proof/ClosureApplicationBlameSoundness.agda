module InterpreterAdequacy.proof.ClosureApplicationBlameSoundness where

-- File Charter:
--   * Converts blame reached while interpreting a closure body into blame for
--     the corresponding syntactic beta application.
--   * Reuses the explicit beta-reification equation for captured environments.
--   * Contains no interpreter recursion or evaluator case analysis.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import InterpreterAdequacy.TraceAgreement
open import InterpreterAdequacy.proof.BetaReification using
  (beta-reification)
open import InterpreterAdequacy.proof.BlameTrace
open import InterpreterAdequacy.proof.SyntaxReification using
  (reified-term)
open import InterpreterAdequacy.proof.TraceAgreementPath using
  (value-trace-rebase)
open import InterpreterAdequacy.proof.TraceAgreementProperties using
  (value-trace-value)
open import NuReduction using (keep; pure-step; β; ↠-step; _—↠[_]_)
import NuTerms as N

closure-application-from-body-blame :
  ∀ {W Z χs}
    {world-agreement : WorldTraceAgreement W χs}
    {M body τ vs U u} →
  body ≡
    N.substˣᵐ (N.extˢˣ (environmentSubstitution vs))
      (N.renameᵗᵐ τ M) →
  ValueTraceAgreement world-agreement [] U u →
  BlameTrace world-agreement (reified-term τ (u ∷ vs) M) Z →
  BlameTrace world-agreement ((N.ƛ body) N.· u) Z
closure-application-from-body-blame
    {M = M} {body = body} {τ = τ} {vs = vs} {u = u}
    reification U-agrees
    (blame-trace changes path body-reduction) =
  blame-trace (keep ∷ changes) (world-trace-keep path)
    (↠-step (pure-step (β (value-trace-value U-agrees)))
      (subst
        (λ Q → Q —↠[ changes ] N.blame)
        (sym (beta-reification {M = M} {M′ = body} τ vs u reification))
        body-reduction))

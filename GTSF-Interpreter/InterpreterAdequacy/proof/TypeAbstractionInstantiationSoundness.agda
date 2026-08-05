module InterpreterAdequacy.proof.TypeAbstractionInstantiationSoundness where

-- File Charter:
--   * Proves the immediate `instantiateValue` return of a semantic
--     type-abstraction sound with respect to `β-Λ•`.
--   * Uses the retained `ClosedValue` provenance to justify semantic name
--     substitution and the explicit type-opening reification equation.
--   * Contains no recursive interpreter proof.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just)
open import Data.Nat using (zero; suc)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import Interpreter using
  ( Name
  ; SealName
  ; Value
  ; World
  ; abstract-name
  ; seal-name
  ; substituteName
  ; lookup
  )
open import InterpreterAdequacy.TraceAgreement
open import InterpreterAdequacy.proof.ClosedValueTrace using
  (closed-value-trace)
open import InterpreterAdequacy.proof.ReturnTrace
open import InterpreterAdequacy.proof.TraceAgreementPath using
  (value-trace-rebase)
open import InterpreterAdequacy.proof.SyntaxReification using
  (reified-term)
open import InterpreterAdequacy.proof.TypeAbstractionBetaReification using
  (extend-after-opening; type-beta-reification)
open import Runtime.InterpreterClosedValueProperties using
  (closed-value-instantiate-head)
open import NuReduction using
  (keep; pure-step; β-Λ•; ↠-refl; ↠-step; _—↠[_]_)
import NuTerms as N
open import proof.Core.Properties.NuTermProperties using
  (renameᵗᵐ-preserves-Value; substˣᵐ-preserves-Value)
open import Types using (extᵗ)

type-environment-instantiate-head :
  ∀ {W χs}
    {world-agreement : WorldTraceAgreement W χs}
    {α θ τ} →
  lookup (visibleTypeNames [] W) zero ≡ just (seal-name α) →
  TypeEnvironmentTraceAgreement world-agreement [] θ τ →
  TypeEnvironmentTraceAgreement world-agreement []
    (seal-name α ∷ θ) (extend-after-opening τ)
type-environment-instantiate-head newest-lookup
    (type-environment-trace-agreement lookup-agrees) =
  type-environment-trace-agreement
    λ where
      {X = zero} refl → newest-lookup
      {X = suc X} name-eq → lookup-agrees name-eq

type-abstraction-instantiation-return-sound :
  ∀ {W χs}
    {world-agreement : WorldTraceAgreement W χs}
    {X α V P} →
  lookup (visibleTypeNames [] W) zero ≡ just (seal-name α) →
  ValueTraceAgreement world-agreement []
    (Interpreter.type-abstraction X V) P →
  ReturnTrace world-agreement (P N.•) W (substituteName X α V)
type-abstraction-instantiation-return-sound {α = α} newest-lookup
    (type-abstraction-trace-agrees
      {X = X} {V = V} {P = P} {raw = raw}
      {γ = γ} {θ = θ} {τ = τ} {vs = vs} {vRaw = vRaw}
      fresh graph θ-agrees γ-agrees no-raw reification vP no-P) =
  return-trace (keep ∷ []) (reified-term (extend-after-opening τ) vs raw)
    (world-trace-keep world-trace-done)
    reduction
    (value-trace-rebase
      (closed-value-trace
        (closed-value-instantiate-head fresh graph)
        (type-environment-instantiate-head
          {α = α} newest-lookup θ-agrees)
        γ-agrees no-raw))
  where
  body =
    N.substˣᵐ (N.↑ᵗᵐ (environmentSubstitution vs))
      (N.renameᵗᵐ (extᵗ τ) raw)

  body-value : N.Value body
  body-value =
    substˣᵐ-preserves-Value _
      (renameᵗᵐ-preserves-Value (extᵗ τ) vRaw)

  canonical-reduction :
    ((N.Λ body) N.•) —↠[ keep ∷ [] ]
      reified-term (extend-after-opening τ) vs raw
  canonical-reduction =
    ↠-step (pure-step (β-Λ• {V = body} body-value))
      (subst
        (λ Q → body N.[ zero ]ᵀ —↠[ [] ] Q)
        (type-beta-reification τ vs raw) ↠-refl)

  reduction :
    (P N.•) —↠[ keep ∷ [] ]
      reified-term (extend-after-opening τ) vs raw
  reduction =
    subst
      (λ Q → Q N.• —↠[ keep ∷ [] ] _)
      (sym reification) canonical-reduction

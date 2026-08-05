module InterpreterAdequacy.proof.ClosedValueTrace where

-- File Charter:
--   * Connects the proof-relevant `closeValue` graph to value trace agreement.
--   * Reifies captured term and type environments explicitly, including the
--     type shift performed beneath nested syntactic type abstractions.
--   * Contains no interpreter recursion and constructs no reduction step.

open import Agda.Builtin.Equality using (refl)
open import Data.List using (List; _∷_)
open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality using (subst)

open import Interpreter using (Name; Value)
open import InterpreterAdequacy.TraceAgreement
open import InterpreterAdequacy.proof.SyntaxReification using
  ( reified-term
  ; reified-term-no-bullet
  ; reified-body-no-bullet
  )
open import Runtime.InterpreterClosedValue
import NuTerms as N
open import proof.Core.Properties.NuTermProperties using
  (renameᵗᵐ-preserves-Value; substˣᵐ-preserves-Value)

closed-value-trace :
  ∀ {W χs}
    {world-agreement : WorldTraceAgreement W χs}
    {Ξ γ θ τ vs V U}
    {vV : N.Value V} →
  ClosedValue γ θ vV U →
  TypeEnvironmentTraceAgreement world-agreement Ξ θ τ →
  EnvironmentTraceAgreement world-agreement Ξ γ vs →
  N.No• V →
  ValueTraceAgreement world-agreement Ξ U (reified-term τ vs V)
closed-value-trace closed-closure θ-agrees γ-agrees (N.no•-ƛ no-N) =
  closure-trace-agrees θ-agrees γ-agrees
    no-N refl
    (reified-body-no-bullet γ-agrees no-N)
closed-value-trace
    {τ = τ} {vs = vs}
    (closed-type-abstraction {V = raw} {X = X} {vV = vRaw}
      body-fresh body)
    θ-agrees γ-agrees (N.no•-Λ no-V) =
  type-abstraction-trace-agrees
    body-fresh body
    θ-agrees γ-agrees no-V refl
    (substˣᵐ-preserves-Value (environmentSubstitution vs)
      (renameᵗᵐ-preserves-Value τ (N.Λ vRaw)))
    (reified-term-no-bullet γ-agrees (N.no•-Λ no-V))
closed-value-trace (closed-constant κ) θ-agrees γ-agrees N.no•-$ =
  constant-trace-agrees
closed-value-trace (closed-tagged body) θ-agrees γ-agrees
    (N.no•-⟨⟩ no-V) =
  tagged-trace-agrees θ-agrees
    (closed-value-trace body θ-agrees γ-agrees no-V)
closed-value-trace (closed-sealed name-eq body) θ-agrees γ-agrees
    (N.no•-⟨⟩ no-V) =
  sealed-trace-agrees
    (TypeEnvironmentTraceAgreement.type-trace-lookup-agrees
      θ-agrees name-eq)
    (closed-value-trace body θ-agrees γ-agrees no-V)
closed-value-trace (closed-function-proxy body) θ-agrees γ-agrees
    (N.no•-⟨⟩ no-V) =
  function-proxy-trace-agrees θ-agrees
    (closed-value-trace body θ-agrees γ-agrees no-V)
closed-value-trace (closed-forall-proxy body) θ-agrees γ-agrees
    (N.no•-⟨⟩ no-V) =
  forall-proxy-trace-agrees θ-agrees
    (closed-value-trace body θ-agrees γ-agrees no-V)
closed-value-trace (closed-generalized body) θ-agrees γ-agrees
    (N.no•-⟨⟩ no-V) =
  generalized-trace-agrees θ-agrees
    (closed-value-trace body θ-agrees γ-agrees no-V)

module InterpreterAdequacy.proof.InterpreterImmediateSoundness where

-- File Charter:
--   * Proves return soundness for interpreter forms that return immediately:
--     variables, closures, closed type abstractions, and constants.
--   * Uses explicit environment reification and the `closeValue` graph.
--   * Leaves applications, primitives, `ν`, and active coercions to the
--     mutually recursive driver.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([])
open import Data.Maybe using (just)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (trans)

open import Interpreter using
  ( Environment
  ; TypeEnvironment
  ; Value
  ; World
  ; closure
  ; constant
  ; closeTypeAbstractionBody
  ; lookup
  )
open import InterpreterAdequacy.TraceAgreement
open import InterpreterAdequacy.proof.ClosedValueTrace using
  (closed-value-trace)
open import InterpreterAdequacy.proof.ReturnTrace
open import InterpreterAdequacy.proof.SyntaxReification using
  ( lookup-environment-trace
  ; reified-body-no-bullet
  ; reified-term
  )
open import Runtime.InterpreterClosedValue using (ClosedValue)
open import NuReduction using (StoreChanges)
import NuTerms as N
open import proof.InterpreterClosedValueProof using (closeValue-closed)

variable-return-sound :
  ∀ {W χs}
    {world-agreement : WorldTraceAgreement W χs}
    {γ θ x P V} →
  TermTraceAgreement world-agreement [] γ θ (N.` x) P →
  lookup γ x ≡ just V →
  ReturnTrace world-agreement P W V
variable-return-sound
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    lookup-eq
    with lookup-environment-trace γ-agrees lookup-eq
variable-return-sound
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    lookup-eq
    | v , (environment-eq , V-agrees) =
  return-trace-refl (trans reification environment-eq) V-agrees

closure-return-sound :
  ∀ {W χs}
    {world-agreement : WorldTraceAgreement W χs}
    {γ θ N P} →
  N.No• N →
  TermTraceAgreement world-agreement [] γ θ (N.ƛ N) P →
  ReturnTrace world-agreement P W (closure N γ θ)
closure-return-sound no-N
    (term-trace-agreement τ vs θ-agrees γ-agrees reification) =
  return-trace-refl reification
    (closure-trace-agrees θ-agrees γ-agrees no-N refl
      (reified-body-no-bullet γ-agrees no-N))

type-abstraction-return-sound :
  ∀ {W χs}
    {world-agreement : WorldTraceAgreement W χs}
    {γ θ V P U}
    {vV : N.Value V} →
  N.No• V →
  TermTraceAgreement world-agreement [] γ θ (N.Λ V) P →
  closeTypeAbstractionBody vV γ θ ≡ just U →
  ReturnTrace world-agreement P W U
type-abstraction-return-sound {vV = vV} no-V
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    close-eq =
  return-trace-refl reification
    (closed-value-trace
      (closeValue-closed (N.Λ vV) close-eq)
      θ-agrees γ-agrees (N.no•-Λ no-V))

constant-return-sound :
  ∀ {W χs}
    {world-agreement : WorldTraceAgreement W χs}
    {γ θ κ P} →
  TermTraceAgreement world-agreement [] γ θ (N.$ κ) P →
  ReturnTrace world-agreement P W (constant κ)
constant-return-sound
    (term-trace-agreement τ vs θ-agrees γ-agrees reification) =
  return-trace-refl reification constant-trace-agrees

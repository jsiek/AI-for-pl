module Runtime.InterpreterClosedValueProperties where

-- File Charter:
--   * Public structural interface for the `ClosedValue` graph.
--   * Exposes scope, abstract-name freshness, and deterministic supply facts.
--   * Delegates proofs to a reduction-free private module.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using (_∷_)
open import Data.List.Membership.Propositional using (_∉_)
open import Data.Maybe using (just)
open import Data.Nat using (_≤_; suc)
open import Data.Product using (Σ-syntax)
open import Coercions using (Inert)

open import Interpreter
open import Runtime.InterpreterClosedValue
open import Narrowing.InterpreterValueNarrowing
open import Narrowing.InterpreterWorldNarrowing
import NuTerms as N
import proof.InterpreterClosedValueStructural as Proof

lookup-seal-allocated :
  ∀ {W θ X α} →
  TypeEnvironmentScoped W θ →
  lookup θ X ≡ just (seal-name α) →
  Allocated W α
lookup-seal-allocated =
  Proof.lookup-seal-allocated

closed-value-scoped :
  ∀ {W γ θ V U}
    {vV : N.Value V} →
  EnvironmentScoped W γ →
  TypeEnvironmentScoped W θ →
  ClosedValue γ θ vV U →
  ValueScoped W U
closed-value-scoped =
  Proof.closed-value-scoped

closed-value-name-fresh :
  ∀ {γ θ V U X}
    {vV : N.Value V} →
  abstract-name X ∉ θ →
  ClosedValue γ θ vV U →
  NameFresh X U
closed-value-name-fresh =
  Proof.closed-value-name-fresh

next-generated-abstract-index :
  ∀ θ →
  nextAbstractIndex
    (abstract-name (nextAbstractName θ) ∷ θ) ≡
    suc (nextAbstractIndex θ)
next-generated-abstract-index =
  Proof.next-generated-abstract-index

abstract-name-fresh-at :
  ∀ {θ X} →
  nextAbstractIndex θ ≤ X →
  abstract-name (type-name X) ∉ θ
abstract-name-fresh-at =
  Proof.abstract-name-fresh-at

next-abstract-fresh-below :
  ∀ {θ θ′} →
  nextAbstractIndex θ′ ≤ nextAbstractIndex θ →
  abstract-name (nextAbstractName θ) ∉ θ′
next-abstract-fresh-below {θ} {θ′} =
  Proof.next-abstract-fresh-below {θ = θ} {θ′ = θ′}

closed-value-instantiate-head :
  ∀ {γ θ V U X α}
    {vV : N.Value V} →
  (fresh : abstract-name X ∉ θ) →
  ClosedValue γ (abstract-name X ∷ θ) vV U →
  ClosedValue γ (seal-name α ∷ θ) vV
    (substituteName X α U)
closed-value-instantiate-head =
  Proof.closed-value-instantiate-head

closed-value-cast-body :
  ∀ {γ θ M U c}
    {vM : N.Value M} {ic : Inert c} →
  ClosedValue γ θ (vM N.⟨ ic ⟩) U →
  Σ[ V ∈ Value ] ClosedValue γ θ vM V
closed-value-cast-body =
  Proof.closed-value-cast-body

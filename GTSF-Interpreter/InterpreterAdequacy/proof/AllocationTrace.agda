module InterpreterAdequacy.proof.AllocationTrace where

-- File Charter:
--   * Connects one interpreter allocation with one small-step `bind` change.
--   * Extends the captured type environment with the freshly allocated seal.
--   * Contains no interpreter recursion and constructs only the allocation
--     prefix required by `ν` and `inst` soundness.

open import Agda.Builtin.Equality using (refl)
open import Data.List using ([]; _∷_; _++_)
open import Data.Maybe using (just)
open import Data.Nat using (zero; suc)

open import Interpreter using
  ( TypeEnvironment
  ; allocate
  ; allocation
  ; lookup
  ; seal-name
  ; seal-name-id
  ; world
  )
open import InterpreterAdequacy.TraceAgreement
open import InterpreterAdequacy.proof.TraceAgreementBind using
  (lookup-after-seal-insertion)
open import InterpreterAdequacy.proof.TraceAgreementProperties using
  (world-trace-agreement-++)
open import NuReduction using (bind)
open import Types using (Renameᵗ; Ty; renameᵗ)

type-environment-trace-world :
  ∀ {W χs}
    {world-agreement : WorldTraceAgreement W χs}
    {θ τ} →
  TypeEnvironmentTraceAgreement world-agreement [] θ τ →
  TypeEnvironmentWorldAgreement [] W θ τ
type-environment-trace-world
    (type-environment-trace-agreement lookup-agrees) =
  type-environment-world-agreement lookup-agrees

allocation-path :
  ∀ {next cells χs θ τ A}
    (world-agreement : WorldTraceAgreement (world next cells) χs) →
  TypeEnvironmentTraceAgreement world-agreement [] θ τ →
  WorldTracePath (world next cells) (bind (renameᵗ τ A) ∷ [])
    (allocate (world next cells) A θ)
allocation-path world-agreement θ-agrees =
  world-trace-bind (type-environment-trace-world θ-agrees) refl
    world-trace-done

allocated-type-environment-agreement :
  ∀ {next cells χs θ τ A}
    (world-agreement : WorldTraceAgreement (world next cells) χs)
    (θ-agrees : TypeEnvironmentTraceAgreement world-agreement [] θ τ) →
  let
    path = allocation-path {A = A} world-agreement θ-agrees
    new-agreement = world-trace-agreement-++ world-agreement path
  in
  TypeEnvironmentTraceAgreement new-agreement []
    (seal-name (seal-name-id next) ∷ θ)
    (λ { zero → zero ; (suc X) → suc (τ X) })
allocated-type-environment-agreement
    {next = next} {cells = cells} {θ = θ} {τ = τ} {A = A}
    world-agreement
    (type-environment-trace-agreement lookup-agrees) =
  type-environment-trace-agreement
    λ where
      {X = zero} refl → refl
      {X = suc X} name-eq →
        lookup-after-seal-insertion []
          {cells = cells} {X = τ X} {a = _}
          {next = next} {A = A} {θ = θ}
          (lookup-agrees name-eq)


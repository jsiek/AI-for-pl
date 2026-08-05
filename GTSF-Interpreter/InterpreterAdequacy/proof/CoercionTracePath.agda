module InterpreterAdequacy.proof.CoercionTracePath where

-- File Charter:
--   * Reindexes a captured type environment and its reified coercion across
--     an arbitrary allocation trace in one induction.
--   * Relates the resulting renaming to `applyCoercions`, which is the action
--     performed by small-step evaluation contexts.
--   * Contains no interpreter recursion and constructs no reduction step.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_; _++_)
open import Data.Nat using (suc)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import Coercions using (Coercion; renameᶜ)
open import Interpreter using (allocation; world)
open import InterpreterAdequacy.TraceAgreement
open import InterpreterAdequacy.proof.TraceAgreementBind using
  (type-environment-trace-bind)
open import InterpreterAdequacy.proof.TraceAgreementPath using
  (type-environment-trace-rebase)
open import InterpreterAdequacy.proof.TraceAgreementProperties using
  (world-trace-agreement-++)
open import NuReduction using (bind; keep)
open import proof.Core.Properties.CoercionProperties using
  (renameᶜ-compose)
open import proof.Core.Properties.ReductionProperties using
  (applyCoercions)
open import Types using (Renameᵗ)

coercion-trace-path :
  ∀ {W U prefix changes θ τ}
    (world-agreement : WorldTraceAgreement W prefix)
    (path : WorldTracePath W changes U) →
  TypeEnvironmentTraceAgreement world-agreement [] θ τ →
  (c : Coercion) →
  Σ[ ρ ∈ Renameᵗ ]
    TypeEnvironmentTraceAgreement
      (world-trace-agreement-++ world-agreement path) [] θ ρ ×
    renameᶜ ρ c ≡ applyCoercions changes (renameᶜ τ c)
coercion-trace-path world-agreement world-trace-done θ-agrees c =
  _ , type-environment-trace-rebase θ-agrees , refl
coercion-trace-path world-agreement (world-trace-keep path)
    θ-agrees c
    with coercion-trace-path world-agreement path θ-agrees c
coercion-trace-path world-agreement (world-trace-keep path)
    θ-agrees c
    | ρ , final-agrees , coercion-eq =
  ρ , type-environment-trace-rebase final-agrees , coercion-eq
coercion-trace-path {θ = θ} {τ = τ} world-agreement
    (world-trace-bind
      {next = next} {cells = cells} {χs = tail} {A = A} {B = B}
      {θ = allocation-θ}
      allocation-agrees type-eq path)
    θ-agrees c
    with coercion-trace-path bind-agreement path θ-after-bind c
  where
  bind-path :
    WorldTracePath (world next cells) (bind B ∷ [])
      (world (suc next)
        (allocation (Interpreter.seal-name-id next) A allocation-θ ∷ cells))
  bind-path =
    world-trace-bind allocation-agrees type-eq world-trace-done

  bind-agreement = world-trace-agreement-++ world-agreement bind-path

  θ-after-bind :
    TypeEnvironmentTraceAgreement bind-agreement [] θ
      (λ X → suc (τ X))
  θ-after-bind = type-environment-trace-bind θ-agrees
coercion-trace-path {θ = θ} {τ = τ} world-agreement
    (world-trace-bind
      {next = next} {cells = cells} {χs = tail} {A = A} {B = B}
      {θ = allocation-θ}
      allocation-agrees type-eq path)
    θ-agrees c
    | ρ , final-agrees , coercion-eq =
  ρ , type-environment-trace-rebase final-agrees ,
  trans coercion-eq
    (cong (applyCoercions tail)
      (sym (renameᶜ-compose τ suc c)))

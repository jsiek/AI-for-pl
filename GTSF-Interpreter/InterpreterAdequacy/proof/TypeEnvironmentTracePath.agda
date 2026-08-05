module InterpreterAdequacy.proof.TypeEnvironmentTracePath where

-- File Charter:
--   * Carries one type-environment agreement across a world trace while
--     proving the induced action on types, coercions, and binder coercions.
--   * Produces all reification equations in one induction so `ν`, casts, and
--     coercion instantiation share one canonical path certificate.
--   * Contains no interpreter recursion and constructs no reduction step.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_; _++_)
open import Data.Nat using (zero; suc)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import Coercions using (Coercion; renameᶜ)
open import Interpreter using (TypeEnvironment; allocation; world)
open import InterpreterAdequacy.TraceAgreement
open import InterpreterAdequacy.proof.TraceAgreementBind using
  (type-environment-trace-bind)
open import InterpreterAdequacy.proof.TraceAgreementPath using
  (type-environment-trace-rebase)
open import InterpreterAdequacy.proof.TraceAgreementProperties using
  (world-trace-agreement-++)
open import NuReduction using (applyTys; bind)
open import proof.Core.Properties.CoercionProperties using
  (renameᶜ-compose; renameᶜ-cong)
open import proof.Core.Properties.ReductionProperties using
  (applyCoercions; applyCoercionUnderTyBinders)
open import proof.Core.Properties.TypeProperties using
  (renameᵗ-compose)
open import Types using (Renameᵗ; Ty; extᵗ; renameᵗ)

record TypeEnvironmentPathAgreement
    {W U prefix changes θ τ}
    (world-agreement : WorldTraceAgreement W prefix)
    (path : WorldTracePath W changes U)
    (initial-agreement :
      TypeEnvironmentTraceAgreement world-agreement [] θ τ) : Set₁ where
  constructor type-environment-path-agreement
  field
    final-renaming : Renameᵗ
    final-agreement :
      TypeEnvironmentTraceAgreement
        (world-trace-agreement-++ world-agreement path)
        [] θ final-renaming
    type-action :
      ∀ A →
      renameᵗ final-renaming A ≡
        applyTys changes (renameᵗ τ A)
    coercion-action :
      ∀ c →
      renameᶜ final-renaming c ≡
        applyCoercions changes (renameᶜ τ c)
    binder-coercion-action :
      ∀ c →
      renameᶜ (extᵗ final-renaming) c ≡
        applyCoercionUnderTyBinders changes
          (renameᶜ (extᵗ τ) c)

open TypeEnvironmentPathAgreement public

ext-compose-suc :
  ∀ τ X →
  extᵗ (λ Y → suc (τ Y)) X ≡ extᵗ suc (extᵗ τ X)
ext-compose-suc τ zero = refl
ext-compose-suc τ (suc X) = refl

type-environment-trace-path :
  ∀ {W U prefix changes θ τ}
    (world-agreement : WorldTraceAgreement W prefix)
    (path : WorldTracePath W changes U)
    (θ-agrees : TypeEnvironmentTraceAgreement world-agreement [] θ τ) →
  TypeEnvironmentPathAgreement world-agreement path θ-agrees
type-environment-trace-path world-agreement world-trace-done θ-agrees =
  type-environment-path-agreement _
    (type-environment-trace-rebase θ-agrees)
    (λ A → refl) (λ c → refl) (λ c → refl)
type-environment-trace-path world-agreement (world-trace-keep path)
    θ-agrees
    with type-environment-trace-path world-agreement path θ-agrees
type-environment-trace-path world-agreement (world-trace-keep path)
    θ-agrees
    | type-environment-path-agreement ρ final types coercions binders =
  type-environment-path-agreement ρ
    (type-environment-trace-rebase final) types coercions binders
type-environment-trace-path {θ = θ} {τ = τ} world-agreement
    (world-trace-bind
      {next = next} {cells = cells} {χs = tail}
      {A = A} {B = B} {θ = allocation-θ}
      allocation-agrees type-eq path)
    θ-agrees =
  type-environment-path-agreement (final-renaming result)
    (type-environment-trace-rebase (final-agreement result))
    (λ C → trans (type-action result C)
      (cong (applyTys tail)
        (sym (renameᵗ-compose τ suc C))))
    (λ c → trans (coercion-action result c)
      (cong (applyCoercions tail)
        (sym (renameᶜ-compose τ suc c))))
    (λ c → trans (binder-coercion-action result c)
      (cong (applyCoercionUnderTyBinders tail)
        (trans
          (renameᶜ-cong (ext-compose-suc τ) c)
          (sym (renameᶜ-compose (extᵗ τ) (extᵗ suc) c)))))
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

  result = type-environment-trace-path bind-agreement path θ-after-bind

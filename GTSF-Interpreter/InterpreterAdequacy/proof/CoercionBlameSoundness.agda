module InterpreterAdequacy.proof.CoercionBlameSoundness where

-- File Charter:
--   * Proves that a runtime ground-tag mismatch corresponds to the official
--     syntactic `tag-untag-bad` blame step after environment reification.
--   * Uses trace-environment lookup agreement to handle nominal seal tags.
--   * Contains no interpreter recursion or evaluator case analysis.

open import Agda.Builtin.Equality using (_≡_; refl)
import Data.Empty
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import Coercions as C
open import Interpreter using
  ( RuntimeGround
  ; allocations
  ; base-ground
  ; function-ground
  ; seal-variable-ground
  ; base-tag
  ; function-tag
  ; variable-tag
  ; just-injective
  ; lookup
  ; runtime-ground-syntax
  ; tagOf
  )
open import InterpreterAdequacy.TraceAgreement
open import InterpreterAdequacy.proof.BlameTrace
open import InterpreterAdequacy.proof.TraceAgreementProperties using
  (value-trace-value)
open import NuReduction using
  (keep; pure-step; tag-untag-bad; ↠-refl; ↠-step)
import NuTerms as N
open import Types using (Ground; renameᵗ)

type-variable-injective :
  ∀ {X Y : ℕ} →
  _≡_ {A = Types.Ty} (Types.＇ X) (Types.＇ Y) →
  X ≡ Y
type-variable-injective refl =
  refl

renamed-ground-equality-tags :
  ∀ {W χs}
    {world-agreement : WorldTraceAgreement W χs}
    {θ σ G H τ ρ expected actual} →
  (runtime-ground : RuntimeGround θ G) →
  (gH : Ground H) →
  TypeEnvironmentTraceAgreement world-agreement [] θ τ →
  TypeEnvironmentTraceAgreement world-agreement [] σ ρ →
  tagOf θ (runtime-ground-syntax runtime-ground) ≡ just expected →
  tagOf σ gH ≡ just actual →
  renameᵗ τ G ≡ renameᵗ ρ H →
  expected ≡ actual
renamed-ground-equality-tags
    {σ = σ}
    (seal-variable-ground {X = X} {α = α} θ-lookup)
    (Types.＇ Y)
    (type-environment-trace-agreement θ-agrees)
    (type-environment-trace-agreement σ-agrees)
    expected-eq actual-eq type-eq
    rewrite θ-lookup
    with lookup σ Y in σ-lookup
renamed-ground-equality-tags
    (seal-variable-ground θ-lookup) (Types.＇ Y)
    θ-agrees σ-agrees expected-eq () type-eq | nothing
renamed-ground-equality-tags
    {W = W} {τ = τ} {ρ = ρ}
    (seal-variable-ground {X = X} {α = α} θ-lookup)
    (Types.＇ Y)
    (type-environment-trace-agreement θ-agrees)
    (type-environment-trace-agreement σ-agrees)
    expected-eq actual-eq type-eq | just name =
  trans (sym (just-injective expected-eq))
    (trans
      (cong variable-tag
        (just-injective
          (trans (sym (θ-agrees θ-lookup))
            (trans
              (cong (lookup (allocationTypeNames (allocations W)))
                (type-variable-injective type-eq))
              (σ-agrees σ-lookup)))))
      (just-injective actual-eq))
renamed-ground-equality-tags
    (seal-variable-ground θ-lookup) (Types.‵ ι)
    θ-agrees σ-agrees expected-eq actual-eq ()
renamed-ground-equality-tags
    (seal-variable-ground θ-lookup) Types.★⇒★
    θ-agrees σ-agrees expected-eq actual-eq ()
renamed-ground-equality-tags (base-ground ι) (Types.＇ Y)
    θ-agrees σ-agrees expected-eq actual-eq ()
renamed-ground-equality-tags (base-ground ι) (Types.‵ ι′)
    θ-agrees σ-agrees expected-eq actual-eq type-eq
    with type-eq
renamed-ground-equality-tags (base-ground ι) (Types.‵ .ι)
    θ-agrees σ-agrees expected-eq actual-eq type-eq | refl =
  trans (sym (just-injective expected-eq)) (just-injective actual-eq)
renamed-ground-equality-tags (base-ground ι) Types.★⇒★
    θ-agrees σ-agrees expected-eq actual-eq ()
renamed-ground-equality-tags function-ground (Types.＇ Y)
    θ-agrees σ-agrees expected-eq actual-eq ()
renamed-ground-equality-tags function-ground (Types.‵ ι)
    θ-agrees σ-agrees expected-eq actual-eq ()
renamed-ground-equality-tags function-ground Types.★⇒★
    θ-agrees σ-agrees expected-eq actual-eq refl =
  trans (sym (just-injective expected-eq)) (just-injective actual-eq)

untag-blame-sound :
  ∀ {W χs G H θ τ σ ρ V v expected actual}
    {world-agreement : WorldTraceAgreement W χs}
    {runtime-ground : RuntimeGround θ G}
    {gH : Ground H} →
  TypeEnvironmentTraceAgreement world-agreement [] θ τ →
  TypeEnvironmentTraceAgreement world-agreement [] σ ρ →
  ValueTraceAgreement world-agreement [] V v →
  tagOf θ (runtime-ground-syntax runtime-ground) ≡ just expected →
  tagOf σ gH ≡ just actual →
  (expected ≡ actual → Data.Empty.⊥) →
  BlameTrace world-agreement
    ((v N.⟨ C.renameᶜ ρ (H C.!) ⟩)
      N.⟨ C.renameᶜ τ (G C.？) ⟩) W
untag-blame-sound
    {G = G} {H = H} {runtime-ground = runtime-ground} {gH = gH}
    θ-agrees σ-agrees V-agrees expected-eq actual-eq mismatch =
  blame-trace (keep ∷ []) (world-trace-keep world-trace-done)
    (↠-step
      (pure-step
        (tag-untag-bad (value-trace-value V-agrees)
          (λ type-eq → mismatch
            (renamed-ground-equality-tags runtime-ground gH
              θ-agrees σ-agrees expected-eq actual-eq (sym type-eq)))))
      ↠-refl)

module InterpreterAdequacy.proof.CoercionEliminationSoundness where

-- File Charter:
--   * Proves successful tag elimination and seal elimination sound.
--   * Uses uniqueness of seal positions in reachable worlds to turn runtime
--     name equality into the de Bruijn equality required by small-step rules.
--   * Contains no recursive interpreter proof.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (zero)
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)

import Coercions as C
open import Interpreter using
  ( RuntimeGround
  ; Tag
  ; TypeEnvironment
  ; Value
  ; World
  ; base-ground
  ; function-ground
  ; lookup
  ; runtime-ground-syntax
  ; seal-name
  ; seal-variable-ground
  ; tagOf
  ; variable-tag
  ; base-tag
  ; function-tag
  )
open import InterpreterAdequacy.TraceAgreement
open import InterpreterAdequacy.proof.ReachableWorldNames using
  (visible-empty-lookup-injective)
open import InterpreterAdequacy.proof.ReturnTrace
open import InterpreterAdequacy.proof.TraceAgreementPath using
  (value-trace-rebase)
open import InterpreterAdequacy.proof.TraceAgreementProperties using
  (value-trace-value)
open import NuReduction using
  (keep; pure-step; seal-unseal; tag-untag-ok; ↠-refl; ↠-step)
import NuTerms as N
open import Types using (Ground; Ty; renameᵗ)

matching-tags-renamed-ground′ :
  ∀ {W χs}
    {world-agreement : WorldTraceAgreement W χs}
    {θ σ G H τ ρ} →
  (runtime-ground : RuntimeGround θ G) →
  (gH : Ground H) →
  TypeEnvironmentTraceAgreement world-agreement [] θ τ →
  TypeEnvironmentTraceAgreement world-agreement [] σ ρ →
  tagOf θ (runtime-ground-syntax runtime-ground) ≡ tagOf σ gH →
  renameᵗ τ G ≡ renameᵗ ρ H
matching-tags-renamed-ground′
    {world-agreement = world-agreement} {σ = σ} {τ = τ} {ρ = ρ}
    (seal-variable-ground {X = X} {α = α} θ-lookup) (Types.＇ Y)
    (type-environment-trace-agreement θ-agrees)
    (type-environment-trace-agreement σ-agrees)
    tag-eq
    rewrite θ-lookup
    with lookup σ Y in σ-lookup
matching-tags-renamed-ground′
    {world-agreement = world-agreement} {τ = τ} {ρ = ρ}
    (seal-variable-ground {X = X} {α = α} θ-lookup) (Types.＇ Y)
    (type-environment-trace-agreement θ-agrees)
    (type-environment-trace-agreement σ-agrees)
    refl | just (seal-name .α) =
  cong Types.＇_
    (visible-empty-lookup-injective world-agreement
      (θ-agrees θ-lookup) (σ-agrees σ-lookup))
matching-tags-renamed-ground′
    (seal-variable-ground θ-lookup) (Types.＇ Y)
    θ-agrees σ-agrees () | nothing
matching-tags-renamed-ground′
    (seal-variable-ground θ-lookup) (Types.＇ Y)
    θ-agrees σ-agrees () | just (Interpreter.abstract-name Z)
matching-tags-renamed-ground′
    (seal-variable-ground θ-lookup) (Types.‵ ι)
    θ-agrees σ-agrees tag-eq
    rewrite θ-lookup
    with tag-eq
matching-tags-renamed-ground′
    (seal-variable-ground θ-lookup) (Types.‵ ι)
    θ-agrees σ-agrees tag-eq | ()
matching-tags-renamed-ground′
    (seal-variable-ground θ-lookup) Types.★⇒★
    θ-agrees σ-agrees tag-eq
    rewrite θ-lookup
    with tag-eq
matching-tags-renamed-ground′
    (seal-variable-ground θ-lookup) Types.★⇒★
    θ-agrees σ-agrees tag-eq | ()
matching-tags-renamed-ground′ {σ = σ} (base-ground ι) (Types.＇ Y)
    θ-agrees σ-agrees tag-eq
    with lookup σ Y
matching-tags-renamed-ground′ (base-ground ι) (Types.＇ Y)
    θ-agrees σ-agrees () | nothing
matching-tags-renamed-ground′ (base-ground ι) (Types.＇ Y)
    θ-agrees σ-agrees () | just name
matching-tags-renamed-ground′ (base-ground ι) (Types.‵ ι′)
    θ-agrees σ-agrees tag-eq
    with tag-eq
matching-tags-renamed-ground′ (base-ground ι) (Types.‵ .ι)
    θ-agrees σ-agrees tag-eq | refl = refl
matching-tags-renamed-ground′ (base-ground ι) Types.★⇒★
    θ-agrees σ-agrees ()
matching-tags-renamed-ground′ {σ = σ} function-ground (Types.＇ Y)
    θ-agrees σ-agrees tag-eq
    with lookup σ Y
matching-tags-renamed-ground′ function-ground (Types.＇ Y)
    θ-agrees σ-agrees () | nothing
matching-tags-renamed-ground′ function-ground (Types.＇ Y)
    θ-agrees σ-agrees () | just name
matching-tags-renamed-ground′ function-ground (Types.‵ ι)
    θ-agrees σ-agrees ()
matching-tags-renamed-ground′ function-ground Types.★⇒★
    θ-agrees σ-agrees refl = refl

matching-tags-renamed-ground :
  ∀ {W χs}
    {world-agreement : WorldTraceAgreement W χs}
    {θ σ G H τ ρ expected actual} →
  (runtime-ground : RuntimeGround θ G) →
  (gH : Ground H) →
  TypeEnvironmentTraceAgreement world-agreement [] θ τ →
  TypeEnvironmentTraceAgreement world-agreement [] σ ρ →
  tagOf θ (runtime-ground-syntax runtime-ground) ≡ just expected →
  tagOf σ gH ≡ just actual →
  expected ≡ actual →
  renameᵗ τ G ≡ renameᵗ ρ H
matching-tags-renamed-ground runtime-ground gH θ-agrees σ-agrees
    expected-eq actual-eq match =
  matching-tags-renamed-ground′ runtime-ground gH θ-agrees σ-agrees
    (trans expected-eq (trans (cong just match) (sym actual-eq)))

untag-return-sound :
  ∀ {W χs G H θ τ σ ρ V v expected actual}
    {world-agreement : WorldTraceAgreement W χs}
    {runtime-ground : RuntimeGround θ G}
    {gH : Ground H} →
  TypeEnvironmentTraceAgreement world-agreement [] θ τ →
  TypeEnvironmentTraceAgreement world-agreement [] σ ρ →
  ValueTraceAgreement world-agreement [] V v →
  tagOf θ (runtime-ground-syntax runtime-ground) ≡ just expected →
  tagOf σ gH ≡ just actual →
  expected ≡ actual →
  ReturnTrace world-agreement
    ((v N.⟨ C.renameᶜ ρ (H C.!) ⟩)
      N.⟨ C.renameᶜ τ (G C.？) ⟩) W V
untag-return-sound {W = W} {G = G} {H = H} {τ = τ} {ρ = ρ}
    {V = V} {v = v} {runtime-ground = runtime-ground} {gH = gH}
    θ-agrees σ-agrees V-agrees expected-eq actual-eq match =
  subst
    (λ K → ReturnTrace _
      ((v N.⟨ C.renameᶜ ρ (H C.!) ⟩) N.⟨ K C.？ ⟩) _ _)
    (sym
      (matching-tags-renamed-ground {G = G} {H = H}
        runtime-ground gH
      θ-agrees σ-agrees expected-eq actual-eq match)
    )
    (return-trace (keep ∷ []) v
      (world-trace-keep world-trace-done)
      (↠-step (pure-step (tag-untag-ok (value-trace-value V-agrees)))
        ↠-refl)
      (value-trace-rebase V-agrees))

unseal-return-sound :
  ∀ {W χs X A B α Y θ τ V v}
    {world-agreement : WorldTraceAgreement W χs} →
  lookup θ X ≡ just (seal-name α) →
  TypeEnvironmentTraceAgreement world-agreement [] θ τ →
  lookup (visibleTypeNames [] W) Y ≡ just (seal-name α) →
  ValueTraceAgreement world-agreement [] V v →
  ReturnTrace world-agreement
    ((v N.⟨ C.seal B Y ⟩)
      N.⟨ C.unseal (τ X) (renameᵗ τ A) ⟩) W V
unseal-return-sound {W = W} {X = X} {A = A} {B = B} {τ = τ}
    {V = V} {v = v} {world-agreement = world-agreement}
    lookup-eq θ-agrees sealed-lookup V-agrees =
  subst
    (λ Z → ReturnTrace _
      ((v N.⟨ C.seal B Z ⟩)
        N.⟨ C.unseal (τ X) (renameᵗ τ A) ⟩) _ _)
    (sym
      (visible-empty-lookup-injective world-agreement sealed-lookup
        (TypeEnvironmentTraceAgreement.type-trace-lookup-agrees
          θ-agrees {X = X} {a = seal-name _} lookup-eq)))
    (return-trace (keep ∷ []) v
      (world-trace-keep world-trace-done)
      (↠-step (pure-step (seal-unseal (value-trace-value V-agrees)))
        ↠-refl)
      (value-trace-rebase V-agrees))

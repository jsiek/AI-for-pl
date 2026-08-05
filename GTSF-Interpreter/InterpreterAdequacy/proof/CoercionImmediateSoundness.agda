module InterpreterAdequacy.proof.CoercionImmediateSoundness where

-- File Charter:
--   * Proves return soundness for identity and inert coercion application.
--   * Reconstructs official syntactic wrapper values without evaluating
--     through them; identity contributes its single pure reduction step.
--   * Leaves sequence, untag, unseal, and instantiation to the recursive
--     coercion simulation.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_; _++_)
open import Data.Maybe using (just)

import Coercions as C
open import Interpreter using
  ( Value
  ; closure
  ; constant
  ; tagged
  ; sealed
  ; function-proxy
  ; type-abstraction
  ; forall-proxy
  ; generalized
  ; RuntimeGround
  ; runtime-ground-syntax
  ; TypeEnvironment
  ; World
  ; lookup
  ; seal-name
  )
open import InterpreterAdequacy.TraceAgreement
open import InterpreterAdequacy.proof.ReturnTrace
open import InterpreterAdequacy.proof.TraceAgreementPath using
  (value-trace-rebase)
open import InterpreterAdequacy.proof.TraceAgreementProperties using
  (value-trace-value)
open import NuReduction using
  (keep; pure-step; β-id; ↠-refl; ↠-step)
import NuTerms as N
open import Types using (Ground; Ty)

identity-return-sound :
  ∀ {W χs A V v}
    {world-agreement : WorldTraceAgreement W χs} →
  ValueTraceAgreement world-agreement [] V v →
  ReturnTrace world-agreement (v N.⟨ C.id A ⟩) W V
identity-return-sound V-agrees =
  return-trace (keep ∷ []) _
    (world-trace-keep world-trace-done)
    (↠-step (pure-step (β-id (value-trace-value V-agrees))) ↠-refl)
    (value-trace-rebase V-agrees)

function-proxy-return-sound :
  ∀ {W χs p q θ τ V v}
    {world-agreement : WorldTraceAgreement W χs} →
  TypeEnvironmentTraceAgreement world-agreement [] θ τ →
  ValueTraceAgreement world-agreement [] V v →
  ReturnTrace world-agreement
    (v N.⟨ C.renameᶜ τ (p C.↦ q) ⟩) W
    (function-proxy p q θ V)
function-proxy-return-sound θ-agrees V-agrees =
  return-trace-refl refl
    (function-proxy-trace-agrees θ-agrees V-agrees)

forall-proxy-return-sound :
  ∀ {W χs c θ τ V v}
    {world-agreement : WorldTraceAgreement W χs} →
  TypeEnvironmentTraceAgreement world-agreement [] θ τ →
  ValueTraceAgreement world-agreement [] V v →
  ReturnTrace world-agreement
    (v N.⟨ C.renameᶜ τ (C.`∀ c) ⟩) W
    (forall-proxy c θ V)
forall-proxy-return-sound θ-agrees V-agrees =
  return-trace-refl refl
    (forall-proxy-trace-agrees θ-agrees V-agrees)

tag-return-sound :
  ∀ {W χs G θ τ V v}
    {world-agreement : WorldTraceAgreement W χs} →
  (runtime-ground : RuntimeGround θ G) →
  TypeEnvironmentTraceAgreement world-agreement [] θ τ →
  ValueTraceAgreement world-agreement [] V v →
  ReturnTrace world-agreement
    (v N.⟨ C.renameᶜ τ (G C.!) ⟩) W
    (tagged (runtime-ground-syntax runtime-ground) θ V)
tag-return-sound runtime-ground θ-agrees V-agrees =
  return-trace-refl refl
    (tagged-trace-agrees θ-agrees V-agrees)

seal-return-sound :
  ∀ {W χs A X α θ τ V v}
    {world-agreement : WorldTraceAgreement W χs} →
  lookup θ X ≡ just (seal-name α) →
  TypeEnvironmentTraceAgreement world-agreement [] θ τ →
  ValueTraceAgreement world-agreement [] V v →
  ReturnTrace world-agreement
    (v N.⟨ C.renameᶜ τ (C.seal A X) ⟩) W
    (sealed α V)
seal-return-sound name-eq θ-agrees V-agrees =
  return-trace-refl refl
    (sealed-trace-agrees
      (TypeEnvironmentTraceAgreement.type-trace-lookup-agrees
        θ-agrees name-eq)
      V-agrees)

generalized-return-sound :
  ∀ {W χs A c θ τ V v}
    {world-agreement : WorldTraceAgreement W χs} →
  TypeEnvironmentTraceAgreement world-agreement [] θ τ →
  ValueTraceAgreement world-agreement [] V v →
  ReturnTrace world-agreement
    (v N.⟨ C.renameᶜ τ (C.gen A c) ⟩) W
    (generalized A c θ V)
generalized-return-sound θ-agrees V-agrees =
  return-trace-refl refl
    (generalized-trace-agrees θ-agrees V-agrees)

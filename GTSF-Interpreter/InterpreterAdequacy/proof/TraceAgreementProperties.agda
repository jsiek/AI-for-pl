module InterpreterAdequacy.proof.TraceAgreementProperties where

-- File Charter:
--   * Supplies structural properties of adequacy trace agreements.
--   * Composes interpreter allocation paths and extracts the official
--     syntactic-value and no-runtime-bullet evidence from value agreement.
--   * Contains no interpreter recursion and proves no reduction simulation.

open import Data.List using ([]; _∷_; _++_)

import Coercions as C
open import Interpreter using (Value; world; RuntimeTypeEnvironment)
open import InterpreterAdequacy.TraceAgreement
open import NuReduction using (StoreChanges)
import NuTerms as N

world-trace-path-++ :
  ∀ {W U Z χs χs′} →
  WorldTracePath W χs U →
  WorldTracePath U χs′ Z →
  WorldTracePath W (χs ++ χs′) Z
world-trace-path-++ world-trace-done U⇒Z = U⇒Z
world-trace-path-++ (world-trace-keep W⇒U) U⇒Z =
  world-trace-keep (world-trace-path-++ W⇒U U⇒Z)
world-trace-path-++
    (world-trace-bind θ-agrees type-eq W⇒U) U⇒Z =
  world-trace-bind θ-agrees type-eq
    (world-trace-path-++ W⇒U U⇒Z)

world-trace-agreement-++ :
  ∀ {W U χs χs′} →
  WorldTraceAgreement W χs →
  WorldTracePath W χs′ U →
  WorldTraceAgreement U (χs ++ χs′)
world-trace-agreement-++ (world-trace-agreement empty⇒W) W⇒U =
  world-trace-agreement (world-trace-path-++ empty⇒W W⇒U)

empty-world-trace-agreement :
  WorldTraceAgreement (world 0 []) []
empty-world-trace-agreement =
  world-trace-agreement world-trace-done

empty-type-environment-trace-agreement :
  ∀ {χs} {world-agreement : WorldTraceAgreement (world 0 []) χs} →
  TypeEnvironmentTraceAgreement
    world-agreement [] [] (λ X → X)
empty-type-environment-trace-agreement =
  type-environment-trace-agreement (λ ())

empty-environment-trace-agreement :
  ∀ {χs} {world-agreement : WorldTraceAgreement (world 0 []) χs} →
  EnvironmentTraceAgreement world-agreement [] [] []
empty-environment-trace-agreement =
  environment-empty-trace-agrees

mutual
  value-trace-value :
    ∀ {W χs}
      {world-agreement : WorldTraceAgreement W χs}
      {Ξ V v} →
    ValueTraceAgreement world-agreement Ξ V v →
    N.Value v
  value-trace-value
      (closure-trace-agrees θ-agrees γ-agrees no-raw
        reification no-body-bullet) =
    N.ƛ _
  value-trace-value constant-trace-agrees =
    N.$ _
  value-trace-value (tagged-trace-agrees θ-agrees V-agrees) =
    value-trace-value V-agrees N.⟨ C._! _ ⟩
  value-trace-value (sealed-trace-agrees name-eq V-agrees) =
    value-trace-value V-agrees N.⟨ C.seal _ _ ⟩
  value-trace-value
      (function-proxy-trace-agrees θ-agrees V-agrees) =
    value-trace-value V-agrees N.⟨ C._↦_ _ _ ⟩
  value-trace-value
      (type-abstraction-trace-agrees
        fresh graph θ-agrees γ-agrees no-raw reification vP no-P) =
    vP
  value-trace-value (forall-proxy-trace-agrees θ-agrees V-agrees) =
    value-trace-value V-agrees N.⟨ C.`∀ _ ⟩
  value-trace-value (generalized-trace-agrees θ-agrees V-agrees) =
    value-trace-value V-agrees N.⟨ C.gen _ _ ⟩

  value-trace-no-bullet :
    ∀ {W χs}
      {world-agreement : WorldTraceAgreement W χs}
      {Ξ V v} →
    ValueTraceAgreement world-agreement Ξ V v →
    N.No• v
  value-trace-no-bullet
      (closure-trace-agrees θ-agrees γ-agrees no-raw
        reification no-body-bullet) =
    N.no•-ƛ no-body-bullet
  value-trace-no-bullet constant-trace-agrees =
    N.no•-$
  value-trace-no-bullet (tagged-trace-agrees θ-agrees V-agrees) =
    N.no•-⟨⟩ (value-trace-no-bullet V-agrees)
  value-trace-no-bullet (sealed-trace-agrees name-eq V-agrees) =
    N.no•-⟨⟩ (value-trace-no-bullet V-agrees)
  value-trace-no-bullet
      (function-proxy-trace-agrees θ-agrees V-agrees) =
    N.no•-⟨⟩ (value-trace-no-bullet V-agrees)
  value-trace-no-bullet
      (type-abstraction-trace-agrees
        fresh graph θ-agrees γ-agrees no-raw reification vP no-P) =
    no-P
  value-trace-no-bullet (forall-proxy-trace-agrees θ-agrees V-agrees) =
    N.no•-⟨⟩ (value-trace-no-bullet V-agrees)
  value-trace-no-bullet (generalized-trace-agrees θ-agrees V-agrees) =
    N.no•-⟨⟩ (value-trace-no-bullet V-agrees)

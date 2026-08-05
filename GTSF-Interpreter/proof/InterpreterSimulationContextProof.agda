module proof.InterpreterSimulationContextProof where

-- File Charter:
--   * Proves weakening for synchronized interpreter runtime configurations.
--   * Projects a related-world extension to its two unary world extensions.
--   * Preserves static-assumption realization, environment typing, and value
--     narrowing without invoking evaluation or reduction.

open import Interpreter
open import Narrowing.InterpreterCoercionNarrowing using
  (InterpreterTypeNarrowing)
open import Narrowing.InterpreterEnvironmentNarrowing
open import Typing.InterpreterSemanticTypingCore
open import Simulation.Core.InterpreterSimulationContext
open import Runtime.InterpreterStoreCorrespondenceRealization
open import Narrowing.InterpreterTermNarrowing
open import Runtime.InterpreterTypeEnvironmentRealization
open import Narrowing.InterpreterWorldNarrowing
open import Narrowing.InterpreterWorldNarrowingProperties
open import Data.Product using (_,_)
import proof.InterpreterSemanticTypingProperties as SemanticProof

open InterpreterValues
open Narrowing.InterpreterTermNarrowing.RelatedWorlds

module EnvironmentProperties =
  Narrowing.InterpreterEnvironmentNarrowing.EnvironmentNarrowing
    interpreterNarrowingLeaves

module WorldProperties =
  Narrowing.InterpreterWorldNarrowingProperties.WorldNarrowingProperties
    InterpreterTypeNarrowing

left-world-extension :
  ∀ {W W′ U U′}
    {R : WorldRelation W W′}
    {S : WorldRelation U U′} →
  Narrowing.InterpreterTermNarrowing.RelatedWorlds.WorldExtension R S →
  Typing.InterpreterSemanticTypingCore.WorldExtension W U
left-world-extension extension-refl =
  world-extension-refl
left-world-extension (extension-both R≤S) =
  world-extension-allocate (left-world-extension R≤S)
left-world-extension (extension-left R≤S) =
  world-extension-allocate (left-world-extension R≤S)
left-world-extension (extension-right R≤S) =
  left-world-extension R≤S
left-world-extension (extension-crossed R≤S) =
  world-extension-allocate
    (world-extension-allocate (left-world-extension R≤S))

right-world-extension :
  ∀ {W W′ U U′}
    {R : WorldRelation W W′}
    {S : WorldRelation U U′} →
  Narrowing.InterpreterTermNarrowing.RelatedWorlds.WorldExtension R S →
  Typing.InterpreterSemanticTypingCore.WorldExtension W′ U′
right-world-extension extension-refl =
  world-extension-refl
right-world-extension (extension-both R≤S) =
  world-extension-allocate (right-world-extension R≤S)
right-world-extension (extension-left R≤S) =
  right-world-extension R≤S
right-world-extension (extension-right R≤S) =
  world-extension-allocate (right-world-extension R≤S)
right-world-extension (extension-crossed R≤S) =
  world-extension-allocate
    (world-extension-allocate (right-world-extension R≤S))

assumption-realization-weaken :
  ∀ {W W′ U U′ R S θ θ′ assumption} →
  (R≤S :
    Narrowing.InterpreterTermNarrowing.RelatedWorlds.WorldExtension
      {W} {W′} R {U} {U′} S) →
  AssumptionRealization R θ θ′ assumption →
  AssumptionRealization S θ θ′ assumption
assumption-realization-weaken R≤S
    (paired-assumption left-at right-at name~name′) =
  paired-assumption left-at right-at
    (WorldProperties.type-name-narrowing-weaken R≤S name~name′)
assumption-realization-weaken R≤S
    (source-dynamic-assumption left-at name-ok) =
  source-dynamic-assumption left-at
    (source-dynamic-name-weaken R≤S name-ok)
  where
  source-dynamic-name-weaken :
    ∀ {W W′ U U′ R S name} →
    (R≤S :
      Narrowing.InterpreterTermNarrowing.RelatedWorlds.WorldExtension
        {W} {W′} R {U} {U′} S) →
    SourceDynamicName R name →
    SourceDynamicName S name
  source-dynamic-name-weaken R≤S source-dynamic-abstract =
    source-dynamic-abstract
  source-dynamic-name-weaken R≤S
      (source-dynamic-seal dynamic) =
    source-dynamic-seal
      (WorldProperties.left-dynamic-seal-weaken R≤S dynamic)

type-environment-realization-weaken :
  ∀ {W W′ U U′ Φ θ θ′}
    {R : WorldRelation W W′}
    {S : WorldRelation U U′} →
  Narrowing.InterpreterTermNarrowing.RelatedWorlds.WorldExtension R S →
  TypeEnvironmentRealization R Φ θ θ′ →
  TypeEnvironmentRealization S Φ θ θ′
type-environment-realization-weaken R≤S realization =
  type-environment-realization
    (WorldProperties.type-environment-narrowing-weaken R≤S
      (environments-narrow realization))
    (λ assumption-at →
      assumption-realization-weaken R≤S
        (realizes-assumption realization assumption-at))

store-correspondence-realization-weaken :
  ∀ {W W′ U U′ Φ Δᴸ Δᴿ ρ θ θ′}
    {R : WorldRelation W W′}
    {S : WorldRelation U U′} →
  Narrowing.InterpreterTermNarrowing.RelatedWorlds.WorldExtension R S →
  StoreCorrespondenceRealization R Φ Δᴸ Δᴿ ρ θ θ′ →
  StoreCorrespondenceRealization S Φ Δᴸ Δᴿ ρ θ θ′
store-correspondence-realization-weaken R≤S realization =
  store-correspondence-realization
    λ corresponds →
      let seal , seal′ , left-at , right-at , seal~seal′ =
            realizes-store-correspondence realization corresponds
      in
      seal , seal′ , left-at , right-at ,
      WorldProperties.seal-link-weaken R≤S seal~seal′

runtime-narrowing-weaken :
  ∀ {W W′ U U′ Φ Δᴸ Δᴿ ρ θ θ′}
    {R : WorldRelation W W′}
    {S : WorldRelation U U′} →
  (R≤S :
    Narrowing.InterpreterTermNarrowing.RelatedWorlds.WorldExtension R S) →
  WorldTyping U →
  WorldTyping U′ →
  RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′ →
  RuntimeNarrowing S Φ Δᴸ Δᴿ ρ θ θ′
runtime-narrowing-weaken R≤S U⊢ U′⊢ runtime =
  runtime-narrowing
    (assumption-membership-unique runtime)
    U⊢ U′⊢
    (SemanticProof.runtime-context-weaken
      (left-world-extension R≤S) (left-runtime-context runtime))
    (SemanticProof.runtime-context-weaken
      (right-world-extension R≤S) (right-runtime-context runtime))
    (right-runtime-environment runtime)
    (store-correspondence-realization-weaken R≤S
      (store-correspondences-realized runtime))
    (type-environment-realization-weaken R≤S
      (type-environments-realized runtime))
    (abstract-supply runtime)

environment-realization-weaken :
  ∀ {W W′ U U′ Φ Δᴸ Δᴿ ρ θ θ′ γᵀ γ γ′}
    {R : WorldRelation W W′}
    {S : WorldRelation U U′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  (R≤S :
    Narrowing.InterpreterTermNarrowing.RelatedWorlds.WorldExtension R S) →
  (U⊢ : WorldTyping U) →
  (U′⊢ : WorldTyping U′) →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  EnvironmentRealization
    (runtime-narrowing-weaken R≤S U⊢ U′⊢ runtime)
    γᵀ γ γ′
environment-realization-weaken R≤S U⊢ U′⊢ environment =
  environment-realization
    (EnvironmentProperties.environment-narrowing-weaken R≤S
      (environments-narrow environment))
    (SemanticProof.environment-weaken
      (left-world-extension R≤S) U⊢
      (left-environment-typed environment))
    (SemanticProof.environment-weaken
      (right-world-extension R≤S) U′⊢
      (right-environment-typed environment))

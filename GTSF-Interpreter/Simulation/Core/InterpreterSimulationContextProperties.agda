module Simulation.Core.InterpreterSimulationContextProperties where

-- File Charter:
--   * Public world-weakening interface for synchronized interpreter contexts.
--   * States the left/right unary projections and the preservation of runtime
--     and term-environment realization explicitly.
--   * Delegates proofs to a reduction-free proof module.

open import Interpreter
open import Typing.InterpreterSemanticTypingCore
open import Simulation.Core.InterpreterSimulationContext
open import Runtime.InterpreterStoreCorrespondenceRealization
open import Narrowing.InterpreterTermNarrowing
open import Runtime.InterpreterTypeEnvironmentRealization
import NuTermImprecision as NTI
import proof.InterpreterSimulationContextProof as Proof
open import ImprecisionWf using (ImpCtx)
open import Types

open Narrowing.InterpreterTermNarrowing.RelatedWorlds

left-world-extension :
  ∀ {W W′ U U′}
    {R : WorldRelation W W′}
    {S : WorldRelation U U′} →
  Narrowing.InterpreterTermNarrowing.RelatedWorlds.WorldExtension R S →
  Typing.InterpreterSemanticTypingCore.WorldExtension W U
left-world-extension =
  Proof.left-world-extension

right-world-extension :
  ∀ {W W′ U U′}
    {R : WorldRelation W W′}
    {S : WorldRelation U U′} →
  Narrowing.InterpreterTermNarrowing.RelatedWorlds.WorldExtension R S →
  Typing.InterpreterSemanticTypingCore.WorldExtension W′ U′
right-world-extension =
  Proof.right-world-extension

type-environment-realization-weaken :
  ∀ {W W′ U U′ Φ θ θ′}
    {R : WorldRelation W W′}
    {S : WorldRelation U U′} →
  Narrowing.InterpreterTermNarrowing.RelatedWorlds.WorldExtension R S →
  TypeEnvironmentRealization R Φ θ θ′ →
  TypeEnvironmentRealization S Φ θ θ′
type-environment-realization-weaken =
  Proof.type-environment-realization-weaken

store-correspondence-realization-weaken :
  ∀ {W W′ U U′ Φ Δᴸ Δᴿ ρ θ θ′}
    {R : WorldRelation W W′}
    {S : WorldRelation U U′} →
  Narrowing.InterpreterTermNarrowing.RelatedWorlds.WorldExtension R S →
  StoreCorrespondenceRealization R Φ Δᴸ Δᴿ ρ θ θ′ →
  StoreCorrespondenceRealization S Φ Δᴸ Δᴿ ρ θ θ′
store-correspondence-realization-weaken =
  Proof.store-correspondence-realization-weaken

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
runtime-narrowing-weaken =
  Proof.runtime-narrowing-weaken

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
environment-realization-weaken =
  Proof.environment-realization-weaken

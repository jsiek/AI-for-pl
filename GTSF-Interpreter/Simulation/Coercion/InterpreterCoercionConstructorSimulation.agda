module Simulation.Coercion.InterpreterCoercionConstructorSimulation where

-- File Charter:
--   * Public terminal simulations for immediate coercion constructors.
--   * Covers paired and one-sided identity, proxy, tag, and generalization.
--   * Delegates explicit computation proofs to a reduction-free proof module.

open import Coercions renaming
  ( id to idᶜ
  ; _↦_ to _↦ᶜ_
  ; `∀ to ∀ᶜ
  ; _! to _!ᶜ
  ; gen to genᶜ
  )
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import Interpreter
open import Narrowing.InterpreterCoercionNarrowing
open import Simulation.Core.InterpreterSimulationContext
open import Simulation.Core.InterpreterSimulationResult
open import Narrowing.InterpreterTermNarrowing
open import Narrowing.InterpreterWorldNarrowing using (TypeEnvironmentScoped)
import NuTermImprecision as NTI
open import Types
import proof.InterpreterCoercionConstructorSimulationProof as Proof

open InterpreterValues
open Narrowing.InterpreterTermNarrowing.RelatedWorlds

paired-id-coercion-simulation :
  ∀ {W W′ θ θ′ A A′ V V′}
    {R : WorldRelation W W′} →
  ValueNarrowing R V V′ →
  TerminalSimulation ValueNarrowing R
    (coerceValue W θ (idᶜ A) V)
    (coerceValue W′ θ′ (idᶜ A′) V′)
paired-id-coercion-simulation =
  Proof.paired-id-coercion-simulation

paired-function-coercion-simulation :
  ∀ {W W′ θ θ′ p p′ q q′ V V′}
    {R : WorldRelation W W′} →
  PersistentSemanticCoercionNarrowing R θ θ′ p p′ →
  PersistentSemanticCoercionNarrowing R θ θ′ q q′ →
  TypeEnvironmentNarrowing R θ θ′ →
  ValueNarrowing R V V′ →
  TerminalSimulation ValueNarrowing R
    (coerceValue W θ (p ↦ᶜ q) V)
    (coerceValue W′ θ′ (p′ ↦ᶜ q′) V′)
paired-function-coercion-simulation =
  Proof.paired-function-coercion-simulation

left-function-coercion-simulation :
  ∀ {W W′ θ p q V V′}
    {R : WorldRelation W W′} →
  PersistentLeftFunctionProxyBoundary R θ p q →
  TypeEnvironmentScoped W θ →
  ValueNarrowing R V V′ →
  TerminalSimulation ValueNarrowing R
    (coerceValue W θ (p ↦ᶜ q) V)
    (immediateReturn W′ V′)
left-function-coercion-simulation =
  Proof.left-function-coercion-simulation

right-function-coercion-simulation :
  ∀ {W W′ θ′ p′ q′ V V′}
    {R : WorldRelation W W′} →
  PersistentRightFunctionProxyBoundary R θ′ p′ q′ →
  TypeEnvironmentScoped W′ θ′ →
  ValueNarrowing R V V′ →
  TerminalSimulation ValueNarrowing R
    (immediateReturn W V)
    (coerceValue W′ θ′ (p′ ↦ᶜ q′) V′)
right-function-coercion-simulation =
  Proof.right-function-coercion-simulation

paired-forall-coercion-simulation :
  ∀ {W W′ θ θ′ c c′ V V′}
    {R : WorldRelation W W′} →
  PersistentSemanticCoercionNarrowing R θ θ′ c c′ →
  TypeEnvironmentNarrowing R θ θ′ →
  ValueNarrowing R V V′ →
  TerminalSimulation ValueNarrowing R
    (coerceValue W θ (∀ᶜ c) V)
    (coerceValue W′ θ′ (∀ᶜ c′) V′)
paired-forall-coercion-simulation =
  Proof.paired-forall-coercion-simulation

left-forall-coercion-simulation :
  ∀ {W W′ θ c V V′}
    {R : WorldRelation W W′} →
  PersistentLeftForallProxyBoundary R θ c →
  TypeEnvironmentScoped W θ →
  ValueNarrowing R V V′ →
  TerminalSimulation ValueNarrowing R
    (coerceValue W θ (∀ᶜ c) V)
    (immediateReturn W′ V′)
left-forall-coercion-simulation =
  Proof.left-forall-coercion-simulation

right-forall-coercion-simulation :
  ∀ {W W′ θ′ c′ V V′}
    {R : WorldRelation W W′} →
  PersistentRightForallProxyBoundary R θ′ c′ →
  TypeEnvironmentScoped W′ θ′ →
  ValueNarrowing R V V′ →
  TerminalSimulation ValueNarrowing R
    (immediateReturn W V)
    (coerceValue W′ θ′ (∀ᶜ c′) V′)
right-forall-coercion-simulation =
  Proof.right-forall-coercion-simulation

paired-tag-coercion-simulation :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ θ θ′ G H V V′}
    {R : WorldRelation W W′} →
  RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′ →
  RuntimeTypeEnvironment θ →
  (G~H : Φ ∣ Δᴸ ⊢ G ⊑ H ⊣ Δᴿ) →
  Ground G →
  Ground H →
  ValueNarrowing R V V′ →
  TerminalSimulation ValueNarrowing R
    (coerceValue W θ (G !ᶜ) V)
    (coerceValue W′ θ′ (H !ᶜ) V′)
paired-tag-coercion-simulation =
  Proof.paired-tag-coercion-simulation

left-tag-coercion-simulation :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ θ θ′ G V V′}
    {R : WorldRelation W W′}
    {gG : Ground G} →
  RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′ →
  RuntimeTypeEnvironment θ →
  (G~★ : Φ ∣ Δᴸ ⊢ G ⊑ ★ ⊣ Δᴿ) →
  ValueNarrowing R V V′ →
  TerminalSimulation ValueNarrowing R
    (coerceValue W θ (G !ᶜ) V)
    (immediateReturn W′ V′)
left-tag-coercion-simulation {gG = gG} =
  Proof.left-tag-coercion-simulation {gG = gG}

right-tag-coercion-simulation :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ θ θ′ H V V′}
    {R : WorldRelation W W′}
    {gH : Ground H} →
  RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′ →
  (★~H : Φ ∣ Δᴸ ⊢ ★ ⊑ H ⊣ Δᴿ) →
  ValueNarrowing R V V′ →
  TerminalSimulation ValueNarrowing R
    (immediateReturn W V)
    (coerceValue W′ θ′ (H !ᶜ) V′)
right-tag-coercion-simulation {gH = gH} =
  Proof.right-tag-coercion-simulation {gH = gH}

paired-generalization-coercion-simulation :
  ∀ {W W′ θ θ′ A A′ c c′ V V′}
    {R : WorldRelation W W′} →
  InterpreterTypeNarrowing A A′ →
  PersistentSemanticCoercionNarrowing R θ θ′ c c′ →
  TypeEnvironmentNarrowing R θ θ′ →
  ValueNarrowing R V V′ →
  TerminalSimulation ValueNarrowing R
    (coerceValue W θ (genᶜ A c) V)
    (coerceValue W′ θ′ (genᶜ A′ c′) V′)
paired-generalization-coercion-simulation =
  Proof.paired-generalization-coercion-simulation

left-generalization-coercion-simulation :
  ∀ {W W′ θ A c V V′}
    {R : WorldRelation W W′} →
  PersistentLeftGeneralizationBoundary R θ A c →
  TypeEnvironmentScoped W θ →
  ValueNarrowing R V V′ →
  TerminalSimulation ValueNarrowing R
    (coerceValue W θ (genᶜ A c) V)
    (immediateReturn W′ V′)
left-generalization-coercion-simulation =
  Proof.left-generalization-coercion-simulation

right-generalization-coercion-simulation :
  ∀ {W W′ θ′ A′ c′ V V′}
    {R : WorldRelation W W′} →
  PersistentRightGeneralizationBoundary R θ′ A′ c′ →
  TypeEnvironmentScoped W′ θ′ →
  ValueNarrowing R V V′ →
  TerminalSimulation ValueNarrowing R
    (immediateReturn W V)
    (coerceValue W′ θ′ (genᶜ A′ c′) V′)
right-generalization-coercion-simulation =
  Proof.right-generalization-coercion-simulation

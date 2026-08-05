module Narrowing.InterpreterSealNarrowing where

-- File Charter:
--   * Exposes paired runtime-seal lookup, construction, and successful checks.
--   * States nominal equality synchronization directly through `WorldRelation`.
--   * Delegates proof scripts to `proof.InterpreterSealNarrowingProof`.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)
open import Data.Maybe using (just)
open import Data.Product using (_×_; Σ-syntax)

open import Coercions renaming
  (seal to sealᶜ; unseal to unsealᶜ)
open import Interpreter
open import Narrowing.InterpreterEnvironmentNarrowing
open import Simulation.Core.InterpreterSimulationResult
open import Narrowing.InterpreterTermNarrowing
open import Narrowing.InterpreterValueNarrowing using (NotSealed)
open import Narrowing.InterpreterWorldNarrowing
import proof.InterpreterSealNarrowingProof as Proof

open InterpreterValues
open Narrowing.InterpreterTermNarrowing.RelatedWorlds

module Environments =
  Narrowing.InterpreterEnvironmentNarrowing.EnvironmentNarrowing
    interpreterNarrowingLeaves

open Environments using (TypeIndexNarrowing)

paired-seal-lookup-forward :
  ∀ {W W′ θ θ′ x x′ α}
    {R : WorldRelation W W′}
    (θ~θ′ : TypeEnvironmentNarrowing R θ θ′) →
  TypeIndexNarrowing θ~θ′ x x′ →
  lookup θ x ≡ just (seal-name α) →
  Σ[ α′ ∈ SealName ]
    lookup θ′ x′ ≡ just (seal-name α′) ×
    SealLink R α α′
paired-seal-lookup-forward =
  Proof.paired-seal-lookup-forward

paired-seal-lookup-backward :
  ∀ {W W′ θ θ′ x x′ α′}
    {R : WorldRelation W W′}
    (θ~θ′ : TypeEnvironmentNarrowing R θ θ′) →
  TypeIndexNarrowing θ~θ′ x x′ →
  lookup θ′ x′ ≡ just (seal-name α′) →
  Σ[ α ∈ SealName ]
    lookup θ x ≡ just (seal-name α) ×
    SealLink R α α′
paired-seal-lookup-backward =
  Proof.paired-seal-lookup-backward

seal-match-forward :
  ∀ {W W′ expected expected′ actual actual′}
    {R : WorldRelation W W′} →
  SealLink R expected expected′ →
  SealLink R actual actual′ →
  expected ≡ actual →
  expected′ ≡ actual′
seal-match-forward =
  Proof.seal-match-forward

seal-match-backward :
  ∀ {W W′ expected expected′ actual actual′}
    {R : WorldRelation W W′} →
  SealLink R expected expected′ →
  SealLink R actual actual′ →
  expected′ ≡ actual′ →
  expected ≡ actual
seal-match-backward =
  Proof.seal-match-backward

target-seal-mismatch-reflects :
  ∀ {W W′ expected expected′ actual actual′}
    {R : WorldRelation W W′} →
  SealLink R expected expected′ →
  SealLink R actual actual′ →
  (expected′ ≡ actual′ → ⊥) →
  expected ≡ actual →
  ⊥
target-seal-mismatch-reflects =
  Proof.target-seal-mismatch-reflects

paired-seal-simulation :
  ∀ {W W′ θ θ′ A A′ x x′ α α′ V V′}
    {R : WorldRelation W W′} →
  lookup θ x ≡ just (seal-name α) →
  lookup θ′ x′ ≡ just (seal-name α′) →
  SealLink R α α′ →
  ValueNarrowing R V V′ →
  TerminalSimulation ValueNarrowing R
    (coerceValue W θ (sealᶜ A x) V)
    (coerceValue W′ θ′ (sealᶜ A′ x′) V′)
paired-seal-simulation =
  Proof.paired-seal-simulation

left-dynamic-seal-simulation :
  ∀ {W W′ θ A x α V V′}
    {R : WorldRelation W W′} →
  lookup θ x ≡ just (seal-name α) →
  LeftDynamicSeal R α →
  NotSealed V′ →
  ValueNarrowing R V V′ →
  TerminalSimulation ValueNarrowing R
    (coerceValue W θ (sealᶜ A x) V)
    (immediateReturn W′ V′)
left-dynamic-seal-simulation =
  Proof.left-dynamic-seal-simulation

paired-unseal-simulation :
  ∀ {W W′ θ θ′ x x′ A A′ expected expected′
     actual actual′ V V′}
    {R : WorldRelation W W′} →
  lookup θ x ≡ just (seal-name expected) →
  lookup θ′ x′ ≡ just (seal-name expected′) →
  SealLink R expected expected′ →
  SealLink R actual actual′ →
  expected ≡ actual →
  ValueNarrowing R V V′ →
  TerminalSimulation ValueNarrowing R
    (coerceValue W θ (unsealᶜ x A) (sealed actual V))
    (coerceValue W′ θ′ (unsealᶜ x′ A′) (sealed actual′ V′))
paired-unseal-simulation =
  Proof.paired-unseal-simulation

left-dynamic-unseal-simulation :
  ∀ {W W′ θ x A expected actual V V′}
    {R : WorldRelation W W′} →
  lookup θ x ≡ just (seal-name expected) →
  LeftDynamicSeal R actual →
  expected ≡ actual →
  ValueNarrowing R V V′ →
  TerminalSimulation ValueNarrowing R
    (coerceValue W θ (unsealᶜ x A) (sealed actual V))
    (immediateReturn W′ V′)
left-dynamic-unseal-simulation =
  Proof.left-dynamic-unseal-simulation

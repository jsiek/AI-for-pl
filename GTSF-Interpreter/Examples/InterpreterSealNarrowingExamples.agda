module Examples.InterpreterSealNarrowingExamples where

-- File Charter:
--   * Checks paired nominal-seal construction and successful checking.
--   * Exercises lookup recovery and the explicit interpreter computations.
--   * Uses concrete interpreter narrowing leaves and related allocated worlds.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just)
open import Data.Nat using (zero; suc)
open import Data.Product using (_×_; Σ-syntax)

open import Coercions renaming
  (seal to sealᶜ; unseal to unsealᶜ)
open import Interpreter
open import Narrowing.InterpreterCoercionNarrowing using
  (InterpreterTypeNarrowing; type-narrowing)
import Narrowing.InterpreterEnvironmentNarrowing
open import Narrowing.InterpreterSealNarrowing
open import Simulation.Core.InterpreterSimulationResult
open import Narrowing.InterpreterTermNarrowing
open import Narrowing.InterpreterWorldNarrowing using ([]-scoped)
open import ImprecisionWf using (idι)
open import Primitives using (κℕ)
open import Types

open InterpreterValues
open Narrowing.InterpreterTermNarrowing.RelatedWorlds

module ExampleEnvironments =
  Narrowing.InterpreterEnvironmentNarrowing.EnvironmentNarrowing
    interpreterNarrowingLeaves

Nat : Ty
Nat =
  ‵ `ℕ

Nat⊑Nat : InterpreterTypeNarrowing Nat Nat
Nat⊑Nat =
  type-narrowing {Φ = []} {Δᴸ = zero} {Δᴿ = zero} idι

offset-worlds :
  WorldRelation
    (allocate emptyWorld Nat [])
    (allocate (allocate emptyWorld Nat []) Nat [])
offset-worlds =
  allocate-both
    (allocate-right-only {A′ = Nat} empty-world⊑ []-scoped)
    Nat⊑Nat []⊑[]ᵗᵉ

fresh-link :
  SealLink offset-worlds
    (seal-name-id zero)
    (seal-name-id (suc zero))
fresh-link =
  link-here

paired-seal-lookup-example :
  Σ[ α′ ∈ SealName ]
    lookup (seal-name (seal-name-id (suc zero)) ∷ []) zero ≡
      just (seal-name α′) ×
    SealLink offset-worlds (seal-name-id zero) α′
paired-seal-lookup-example =
  paired-seal-lookup-forward
    (seal-name⊑ fresh-link ∷⊑∷ᵗᵉ []⊑[]ᵗᵉ)
    ExampleEnvironments.here-both refl

seal-construction-example :
  TerminalSimulation ValueNarrowing offset-worlds
    (coerceValue
      (allocate emptyWorld Nat [])
      (seal-name (seal-name-id zero) ∷ [])
      (sealᶜ Nat zero)
      (constant (κℕ 7)))
    (coerceValue
      (allocate (allocate emptyWorld Nat []) Nat [])
      (seal-name (seal-name-id (suc zero)) ∷ [])
      (sealᶜ Nat zero)
      (constant (κℕ 7)))
seal-construction-example =
  paired-seal-simulation refl refl fresh-link
    (constant⊑ (κℕ 7))

seal-check-example :
  TerminalSimulation ValueNarrowing offset-worlds
    (coerceValue
      (allocate emptyWorld Nat [])
      (seal-name (seal-name-id zero) ∷ [])
      (unsealᶜ zero Nat)
      (sealed (seal-name-id zero) (constant (κℕ 7))))
    (coerceValue
      (allocate (allocate emptyWorld Nat []) Nat [])
      (seal-name (seal-name-id (suc zero)) ∷ [])
      (unsealᶜ zero Nat)
      (sealed (seal-name-id (suc zero)) (constant (κℕ 7))))
seal-check-example =
  paired-unseal-simulation
    refl refl fresh-link fresh-link refl
    (constant⊑ (κℕ 7))

seal-check-result :
  coerceValue
    (allocate emptyWorld Nat [])
    (seal-name (seal-name-id zero) ∷ [])
    (unsealᶜ zero Nat)
    (sealed (seal-name-id zero) (constant (κℕ 7)))
    (suc zero) ≡
  returned
    (allocate emptyWorld Nat [])
    (constant (κℕ 7))
seal-check-result =
  refl

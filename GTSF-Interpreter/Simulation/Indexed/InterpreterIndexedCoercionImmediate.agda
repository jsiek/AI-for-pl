module Simulation.Indexed.InterpreterIndexedCoercionImmediate where

-- File Charter:
--   * Exposes exact indexed simulations for inert coercion constructors.
--   * Retains executable component plans in every returned proxy origin.
--   * Delegates value construction and typing to a focused proof module.

open import Agda.Builtin.Equality using (_≡_)
open import Coercions using (Coercion; _↦_; `∀; gen)
import Data.Nat
open import Data.Nat using (suc)
open import Data.Bool using (true)
open import ImprecisionWf using
  (NonVar; _∣_⊢_⊑_⊣_; _↦_; ∀ⁱ_; ν)
open import Interpreter
open import Narrowing.InterpreterCoercionNarrowing
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Narrowing.InterpreterOperationalValueNarrowing
open import Narrowing.InterpreterReachableCoercionNarrowing using
  (ReachableComponentCoercionNarrowing)
open import Typing.InterpreterSemanticTypingCore using (_⇒ᵛ_; ⟦_⟧[_])
open import Simulation.Core.InterpreterSimulationContext
open import Simulation.Core.InterpreterSimulationResult using (immediateReturn)
open import Narrowing.InterpreterTermNarrowing
import NuTermImprecision as NTI
open import proof.MaximalLowerBoundsWf using (∀ᵢᶜ)
import proof.InterpreterIndexedCoercionImmediateProof as Proof
open import Types

open Narrowing.InterpreterTermNarrowing.RelatedWorlds

indexed-paired-function-coercion :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ ρ θ θ′
      A A′ B B′ C C′ D D′ pA pB pC pD
      c d c′ d′ V V′}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (action :
    ReachableComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
      (apply-coercion (c ↦ d)) (apply-coercion (c′ ↦ d′))
      {A ⇒ B} {A′ ⇒ B′} {C ⇒ D} {C′ ⇒ D′}
      (pA ImprecisionWf.↦ pB) (pC ImprecisionWf.↦ pD)) →
  OperationalValueNarrowing
    (⟦ A ⟧[ θ ] ⇒ᵛ ⟦ B ⟧[ θ ])
    (⟦ A′ ⟧[ θ′ ] ⇒ᵛ ⟦ B′ ⟧[ θ′ ]) R V V′ →
  IndexedTerminalSimulation
    (OperationalValueResult
      (⟦ C ⟧[ θ ] ⇒ᵛ ⟦ D ⟧[ θ ])
      (⟦ C′ ⟧[ θ′ ] ⇒ᵛ ⟦ D′ ⟧[ θ′ ]))
    R
    (coerceValue W θ (c ↦ d) V)
    (coerceValue W′ θ′ (c′ ↦ d′) V′)
    (suc left-index) (suc right-index)
indexed-paired-function-coercion =
  Proof.indexed-paired-function-coercion

indexed-left-function-coercion :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ ρ θ θ′
      A B C D T₁ T₂ pA pB pC pD c d V V′}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (action :
    ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
      (apply-coercion (c ↦ d)) skip-coercion
      {A ⇒ B} {T₁ ⇒ T₂} {C ⇒ D} {T₁ ⇒ T₂}
      (pA ImprecisionWf.↦ pB) (pC ImprecisionWf.↦ pD)) →
  OperationalValueNarrowing
    (⟦ A ⟧[ θ ] ⇒ᵛ ⟦ B ⟧[ θ ])
    (⟦ T₁ ⟧[ θ′ ] ⇒ᵛ ⟦ T₂ ⟧[ θ′ ]) R V V′ →
  IndexedTerminalSimulation
    (OperationalValueResult
      (⟦ C ⟧[ θ ] ⇒ᵛ ⟦ D ⟧[ θ ])
      (⟦ T₁ ⟧[ θ′ ] ⇒ᵛ ⟦ T₂ ⟧[ θ′ ]))
    R
    (coerceValue W θ (c ↦ d) V)
    (immediateReturn W′ V′)
    (suc left-index) right-index
indexed-left-function-coercion =
  Proof.indexed-left-function-coercion

indexed-right-function-coercion :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ ρ θ θ′
      S₁ S₂ A′ B′ C′ D′ pA pB pC pD c′ d′ V V′}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (action :
    ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
      skip-coercion (apply-coercion (c′ ↦ d′))
      {S₁ ⇒ S₂} {A′ ⇒ B′} {S₁ ⇒ S₂} {C′ ⇒ D′}
      (pA ImprecisionWf.↦ pB) (pC ImprecisionWf.↦ pD)) →
  OperationalValueNarrowing
    (⟦ S₁ ⟧[ θ ] ⇒ᵛ ⟦ S₂ ⟧[ θ ])
    (⟦ A′ ⟧[ θ′ ] ⇒ᵛ ⟦ B′ ⟧[ θ′ ]) R V V′ →
  IndexedTerminalSimulation
    (OperationalValueResult
      (⟦ S₁ ⟧[ θ ] ⇒ᵛ ⟦ S₂ ⟧[ θ ])
      (⟦ C′ ⟧[ θ′ ] ⇒ᵛ ⟦ D′ ⟧[ θ′ ]))
    R
    (immediateReturn W V)
    (coerceValue W′ θ′ (c′ ↦ d′) V′)
    left-index (suc right-index)
indexed-right-function-coercion =
  Proof.indexed-right-function-coercion

indexed-paired-forall-coercion :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ ρ θ θ′
      A A′ B B′ p q c c′ V V′}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (action :
    ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
      (apply-coercion (`∀ c)) (apply-coercion (`∀ c′))
      {`∀ A} {`∀ A′} {`∀ B} {`∀ B′} (∀ⁱ p) (∀ⁱ q)) →
  OperationalValueNarrowing
    ⟦ `∀ A ⟧[ θ ] ⟦ `∀ A′ ⟧[ θ′ ] R V V′ →
  IndexedTerminalSimulation
    (OperationalValueResult
      ⟦ `∀ B ⟧[ θ ] ⟦ `∀ B′ ⟧[ θ′ ])
    R
    (coerceValue W θ (`∀ c) V)
    (coerceValue W′ θ′ (`∀ c′) V′)
    (suc left-index) (suc right-index)
indexed-paired-forall-coercion =
  Proof.indexed-paired-forall-coercion

indexed-left-forall-coercion :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ ρ θ θ′
      A T B p q c V V′}
    {nonvar : NonVar A} {occ : occurs Data.Nat.zero A ≡ true}
    {nonvar′ : NonVar B} {occ′ : occurs Data.Nat.zero B ≡ true}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (action :
    ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
      (apply-coercion (`∀ c)) skip-coercion
      {`∀ A} {T} {`∀ B} {T}
      (ν nonvar occ p) (ν nonvar′ occ′ q)) →
  OperationalValueNarrowing
    ⟦ `∀ A ⟧[ θ ] ⟦ T ⟧[ θ′ ] R V V′ →
  IndexedTerminalSimulation
    (OperationalValueResult
      ⟦ `∀ B ⟧[ θ ] ⟦ T ⟧[ θ′ ])
    R
    (coerceValue W θ (`∀ c) V)
    (immediateReturn W′ V′)
    (suc left-index) right-index
indexed-left-forall-coercion =
  Proof.indexed-left-forall-coercion

indexed-right-forall-coercion :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ ρ θ θ′
      A A′ B′ p q c′ V V′}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (action :
    ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
      skip-coercion (apply-coercion (`∀ c′))
      {`∀ A} {`∀ A′} {`∀ A} {`∀ B′} (∀ⁱ p) (∀ⁱ q)) →
  OperationalValueNarrowing
    ⟦ `∀ A ⟧[ θ ] ⟦ `∀ A′ ⟧[ θ′ ] R V V′ →
  IndexedTerminalSimulation
    (OperationalValueResult
      ⟦ `∀ A ⟧[ θ ] ⟦ `∀ B′ ⟧[ θ′ ])
    R
    (immediateReturn W V)
    (coerceValue W′ θ′ (`∀ c′) V′)
    left-index (suc right-index)
indexed-right-forall-coercion =
  Proof.indexed-right-forall-coercion

indexed-paired-generalization-coercion :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ ρ θ θ′
      A A′ B B′ p q C C′ c c′ V V′}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (action :
    ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
      (apply-coercion (gen C c)) (apply-coercion (gen C′ c′))
      {A} {A′} {`∀ B} {`∀ B′} p (∀ⁱ q)) →
  OperationalValueNarrowing
    ⟦ A ⟧[ θ ] ⟦ A′ ⟧[ θ′ ] R V V′ →
  IndexedTerminalSimulation
    (OperationalValueResult
      ⟦ `∀ B ⟧[ θ ] ⟦ `∀ B′ ⟧[ θ′ ])
    R
    (coerceValue W θ (gen C c) V)
    (coerceValue W′ θ′ (gen C′ c′) V′)
    (suc left-index) (suc right-index)
indexed-paired-generalization-coercion =
  Proof.indexed-paired-generalization-coercion

indexed-left-generalization-coercion :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ ρ θ θ′
      A T B p q C c V V′}
    {nonvar : NonVar B} {occ : occurs Data.Nat.zero B ≡ true}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (action :
    ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
      (apply-coercion (gen C c)) skip-coercion
      {A} {T} {`∀ B} {T} p (ν nonvar occ q)) →
  OperationalValueNarrowing
    ⟦ A ⟧[ θ ] ⟦ T ⟧[ θ′ ] R V V′ →
  IndexedTerminalSimulation
    (OperationalValueResult
      ⟦ `∀ B ⟧[ θ ] ⟦ T ⟧[ θ′ ])
    R
    (coerceValue W θ (gen C c) V)
    (immediateReturn W′ V′)
    (suc left-index) right-index
indexed-left-generalization-coercion =
  Proof.indexed-left-generalization-coercion

indexed-right-generalization-coercion :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ ρ θ θ′
      S A′ B′ p q C′ c′ V V′}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (action :
    ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
      skip-coercion (apply-coercion (gen C′ c′))
      {S} {A′} {S} {`∀ B′} p q) →
  OperationalValueNarrowing
    ⟦ S ⟧[ θ ] ⟦ A′ ⟧[ θ′ ] R V V′ →
  IndexedTerminalSimulation
    (OperationalValueResult
      ⟦ S ⟧[ θ ] ⟦ `∀ B′ ⟧[ θ′ ])
    R
    (immediateReturn W V)
    (coerceValue W′ θ′ (gen C′ c′) V′)
    left-index (suc right-index)
indexed-right-generalization-coercion =
  Proof.indexed-right-generalization-coercion

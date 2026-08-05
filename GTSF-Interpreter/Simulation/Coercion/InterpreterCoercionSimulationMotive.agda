module Simulation.Coercion.InterpreterCoercionSimulationMotive where

-- File Charter:
--   * Defines the computation and typed simulation motive for coercion actions.
--   * Makes skipped one-sided actions explicit at the interpreter boundary.
--   * Contains no simulation proof, recursive driver, or reduction semantics.

open import Coercions using (Coercion)
open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import Interpreter
open import Narrowing.InterpreterCoercionNarrowing
open import Typing.InterpreterSemanticTypingCore
open import Simulation.Core.InterpreterSimulationContext
open import Simulation.Core.InterpreterSimulationResult
open import Narrowing.InterpreterTermNarrowing
open import Narrowing.InterpreterTypedValueNarrowing
import NuTermImprecision as NTI
open import Types

open Narrowing.InterpreterTermNarrowing.RelatedWorlds

executeCoercionAction :
  World →
  TypeEnvironment →
  CoercionAction →
  Value →
  Computation
executeCoercionAction W θ skip-coercion V =
  immediateReturn W V
executeCoercionAction W θ (apply-coercion c) V =
  coerceValue W θ c V

CoercionSimulation : Set₂
CoercionSimulation =
  ∀ {W W′ Φ Δᴸ Δᴿ ρ θ θ′ A A′ B B′ p q left right V V′}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  OperationalCoercionNarrowing Φ Δᴸ Δᴿ ρ
    left right {A} {A′} {B} {B′} p q →
  TypedValueNarrowing
    ⟦ A ⟧[ θ ] ⟦ A′ ⟧[ θ′ ] R V V′ →
  TerminalSimulation
    (TypedValueResult ⟦ B ⟧[ θ ] ⟦ B′ ⟧[ θ′ ])
    R
    (executeCoercionAction W θ left V)
    (executeCoercionAction W′ θ′ right V′)

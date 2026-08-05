module Simulation.Directional.InterpreterDirectionalDriverBundle where

-- File Charter:
--   * Packages one complete fuel layer of the constructive simulation.
--   * Keeps the three terminal directions and every mutually recursive
--     interpreter operation visible as separate fields.
--   * Provides the zero-fuel layer from direct interpreter equations.
--   * Contains no positive-fuel recursion, reduction, or catch-up theorem.

open import Data.Nat using (zero)

open import Interpreter using (StepIndex)
open import Simulation.Directional.InterpreterDirectionalSimulationMotive
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Simulation.Coercion.InterpreterOperationalQuotientSimulationMotive
import proof.InterpreterDirectionalZero as Zero


record DirectionalDriverBundle (index : StepIndex) : Set₂ where
  constructor directional-driver-bundle
  field
    coercion-forward :
      FramedDirectionalCoercionSimulation forward-direction index
    coercion-backward :
      FramedDirectionalCoercionSimulation backward-direction index
    coercion-target-blame :
      FramedDirectionalCoercionSimulation target-blame-direction index

    application-forward :
      FramedDirectionalApplyValueSimulation forward-direction index
    application-backward :
      FramedDirectionalApplyValueSimulation backward-direction index
    application-target-blame :
      FramedDirectionalApplyValueSimulation target-blame-direction index

    operational-application-forward :
      DirectionalApplyValueSimulation forward-direction index
    operational-application-backward :
      DirectionalApplyValueSimulation backward-direction index
    operational-application-target-blame :
      DirectionalApplyValueSimulation target-blame-direction index

    paired-instantiation-forward :
      FramedDirectionalPairedInstantiateValueSimulation
        forward-direction index
    paired-instantiation-backward :
      FramedDirectionalPairedInstantiateValueSimulation
        backward-direction index
    paired-instantiation-target-blame :
      FramedDirectionalPairedInstantiateValueSimulation
        target-blame-direction index

    left-instantiation-forward :
      FramedDirectionalLeftInstantiateValueSimulation
        forward-direction index
    left-instantiation-backward :
      FramedDirectionalLeftInstantiateValueSimulation
        backward-direction index
    left-instantiation-target-blame :
      FramedDirectionalLeftInstantiateValueSimulation
        target-blame-direction index

    quotient-down-forward :
      DirectionalQuotientDownSimulation forward-direction index
    quotient-down-backward :
      DirectionalQuotientDownSimulation backward-direction index
    quotient-down-target-blame :
      DirectionalQuotientDownSimulation target-blame-direction index

    quotient-up-forward :
      DirectionalQuotientUpSimulation forward-direction index
    quotient-up-backward :
      DirectionalQuotientUpSimulation backward-direction index
    quotient-up-target-blame :
      DirectionalQuotientUpSimulation target-blame-direction index

    term-forward :
      ∀ {Φ Δᴸ Δᴿ ρ γ N N′ A B p} →
      FramedDirectionalInterpreterTermSimulation
        forward-direction index Φ Δᴸ Δᴿ ρ γ N N′ A B p
    term-backward :
      ∀ {Φ Δᴸ Δᴿ ρ γ N N′ A B p} →
      FramedDirectionalInterpreterTermSimulation
        backward-direction index Φ Δᴸ Δᴿ ρ γ N N′ A B p
    term-target-blame :
      ∀ {Φ Δᴸ Δᴿ ρ γ N N′ A B p} →
      FramedDirectionalInterpreterTermSimulation
        target-blame-direction index Φ Δᴸ Δᴿ ρ γ N N′ A B p

open DirectionalDriverBundle public


zero-directional-driver-bundle :
  DirectionalDriverBundle zero
zero-directional-driver-bundle =
  directional-driver-bundle
    Zero.framed-coercion-forward-zero
    Zero.framed-coercion-backward-zero
    Zero.framed-coercion-target-blame-zero
    Zero.framed-apply-forward-zero
    Zero.framed-apply-backward-zero
    Zero.framed-apply-target-blame-zero
    Zero.apply-forward-zero
    Zero.apply-backward-zero
    Zero.apply-target-blame-zero
    Zero.framed-paired-instantiation-forward-zero
    Zero.framed-paired-instantiation-backward-zero
    Zero.framed-paired-instantiation-target-blame-zero
    Zero.framed-left-instantiation-forward-zero
    Zero.framed-left-instantiation-backward-zero
    Zero.framed-left-instantiation-target-blame-zero
    Zero.quotient-down-forward-zero
    Zero.quotient-down-backward-zero
    Zero.quotient-down-target-blame-zero
    Zero.quotient-up-forward-zero
    Zero.quotient-up-backward-zero
    Zero.quotient-up-target-blame-zero
    Zero.framed-term-forward-zero
    Zero.framed-term-backward-zero
    Zero.framed-term-target-blame-zero

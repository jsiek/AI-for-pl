module Simulation.Coercion.InterpreterCoercionSequenceSimulation where

-- File Charter:
--   * Public asynchronous composition theorem for coercion sequencing.
--   * States all unary typings and recursive simulation hypotheses directly.
--   * Delegates the reduction-free proof to a focused proof module.

open import Coercions using
  (ModeEnv; Coercion; _∣_∣_⊢_∶_=⇒_)
open import Interpreter
open import Typing.InterpreterSemanticTypingCore using (⟦_⟧[_])
open import Simulation.Core.InterpreterSimulationContext
open import Simulation.Core.InterpreterSimulationResult
open import Narrowing.InterpreterTermNarrowing
open import Narrowing.InterpreterTypedValueNarrowing
import NuTermImprecision as NTI
import proof.InterpreterCoercionSequenceSimulationProof as Proof
open import Types

open Narrowing.InterpreterTermNarrowing.RelatedWorlds

paired-sequence-coercion-simulation :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ θ θ′
      A B C A′ B′ C′ c d c′ d′ μ μ′ V V′}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  μ ∣ Δᴸ ∣ NTI.leftStoreⁱ ρ ⊢ c ∶ A =⇒ B →
  μ ∣ Δᴸ ∣ NTI.leftStoreⁱ ρ ⊢ d ∶ B =⇒ C →
  μ′ ∣ Δᴿ ∣ NTI.rightStoreⁱ ρ ⊢ c′ ∶ A′ =⇒ B′ →
  μ′ ∣ Δᴿ ∣ NTI.rightStoreⁱ ρ ⊢ d′ ∶ B′ =⇒ C′ →
  TypedValueNarrowing
    ⟦ A ⟧[ θ ] ⟦ A′ ⟧[ θ′ ] R V V′ →
  (head-simulation :
    TerminalSimulation
      (TypedValueResult ⟦ B ⟧[ θ ] ⟦ B′ ⟧[ θ′ ])
      R
      (coerceValue W θ c V)
      (coerceValue W′ θ′ c′ V′)) →
  (∀ {U U′ Q Q′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    TypedValueNarrowing
      ⟦ B ⟧[ θ ] ⟦ B′ ⟧[ θ′ ] S Q Q′ →
    TerminalSimulation
      (TypedValueResult ⟦ C ⟧[ θ ] ⟦ C′ ⟧[ θ′ ])
      S
      (coerceValue U θ d Q)
      (coerceValue U′ θ′ d′ Q′)) →
  TerminalSimulation
    (TypedValueResult ⟦ C ⟧[ θ ] ⟦ C′ ⟧[ θ′ ])
    R
    (coerceValue W θ (c Coercions.︔ d) V)
    (coerceValue W′ θ′ (c′ Coercions.︔ d′) V′)
paired-sequence-coercion-simulation =
  Proof.paired-sequence-coercion-simulation

module proof.InterpreterCoercionSequenceSimulationProof where

-- File Charter:
--   * Composes two paired coercion simulations through explicit sequencing.
--   * Joins independently delayed phase results using terminal simulation.
--   * Excludes target errors by unary coercion typing, without reductions.

open import Agda.Builtin.Equality using (_≡_)
import Data.Empty
open import Coercions using
  (ModeEnv; Coercion; cast-seq; _∣_∣_⊢_∶_=⇒_)
open import Relation.Binary.PropositionalEquality using (trans)

open import Interpreter
open import Simulation.Coercion.InterpreterCoercionComputation
open import Typing.InterpreterCoercionSemanticTyping
open import Core.InterpreterFuel using (coerceValue-terminal-stable)
open import Typing.InterpreterSemanticTypingCore using (⟦_⟧[_])
open import Simulation.Core.InterpreterSimulationContext
open import Simulation.Core.InterpreterSimulationResult
open import Narrowing.InterpreterTermNarrowing
open import Narrowing.InterpreterTypedValueNarrowing
open import proof.InterpreterSequenceSimulation using
  (sequence-simulation)
open import proof.InterpreterSimulationTransport using
  (simulation-pointwise)
open import Types
import NuTermImprecision as NTI

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
paired-sequence-coercion-simulation
    {W = W} {W′ = W′} {θ = θ} {θ′ = θ′}
    {c = c} {d = d} {c′ = c′} {d′ = d′}
    {V = V} {V′ = V′} {R = R}
    runtime c⊢ d⊢ c′⊢ d′⊢ V~V′
    head-simulation continuation-simulation =
  simulation-pointwise
    (coerce-sequence-computation
      {W = W} {θ = θ} {c = c} {d = d} {V = V})
    (coerce-sequence-computation
      {W = W′} {θ = θ′} {c = c′} {d = d′} {V = V′})
    (sequence-simulation
      {W = W} {W′ = W′} {R = R}
      {left-head = coerceValue W θ c V}
      {right-head = coerceValue W′ θ′ c′ V′}
      {left-continuation =
        λ U Q → coerceValue U θ d Q}
      {right-continuation =
        λ U′ Q′ → coerceValue U′ θ′ d′ Q′}
      head-simulation continuation-simulation
      (λ U Q {n} {o} terminal eq k →
        coerceValue-terminal-stable
          {W = U} {θ = θ} {c = d} {V = Q} {n = n}
          terminal eq k)
      (λ U′ Q′ {n} {o} terminal eq k →
        coerceValue-terminal-stable
          {W = U′} {θ = θ′} {c = d′} {V = Q′} {n = n}
          terminal eq k)
      (λ { {n} {Z′} {e} eq →
        right-sequence-error-free {n = n} {U′ = Z′} {e = e} eq
        }))
  where
  right-sequence-error-free :
    ∀ {n U′ e} →
    sequence W′
      (coerceValue W′ θ′ c′ V′)
      (λ Z′ Q′ → coerceValue Z′ θ′ d′ Q′)
      n
      ≡ failed U′ e →
    Data.Empty.⊥
  right-sequence-error-free {n} eq =
    coerceValue-never-fails n
      (right-world-typed runtime)
      (right-runtime-context runtime)
      (cast-seq c′⊢ d′⊢)
      (right-value-typed V~V′)
      (trans
        (coerce-sequence-computation
          {W = W′} {θ = θ′}
          {c = c′} {d = d′} {V = V′} n)
        eq)

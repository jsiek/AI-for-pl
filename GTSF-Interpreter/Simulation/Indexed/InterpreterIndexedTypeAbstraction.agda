module Simulation.Indexed.InterpreterIndexedTypeAbstraction where

-- File Charter:
--   * Exposes indexed simulation for compiler-aligned paired type
--     abstractions.
--   * Closes both syntactic values explicitly and returns their exact
--     operational value origin.
--   * Delegates the reduction-free proof to a focused private module.

open import Agda.Builtin.Equality using (_≡_)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import Interpreter
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Narrowing.InterpreterOperationalValueNarrowing
open import Typing.InterpreterSemanticTypingCore using (⟦_⟧[_])
open import Simulation.Core.InterpreterSimulationContext
open import Narrowing.InterpreterTermNarrowing
import NuTermImprecision as NTI
import NuTerms as N
import proof.InterpreterIndexedTypeAbstractionProof as Proof
open import Types

open Narrowing.InterpreterTermNarrowing.RelatedWorlds

indexed-paired-type-abstraction-simulation :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ ρ γᵀ
      θ θ′ γ γ′ V V′ A B p}
    {R : WorldRelation W W′} →
  (alignment :
    AlignedInterpreterTermNarrowing
      Φ Δᴸ Δᴿ ρ γᵀ
      (N.Λ V) (N.Λ V′) (`∀ A) (`∀ B) p) →
  aligned-term-root alignment ≡ paired-type-abstraction-rootᴬ →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  OperationalEnvironmentNarrowing θ θ′ R γᵀ γ γ′ →
  IndexedTerminalSimulation
    (OperationalValueResult
      ⟦ `∀ A ⟧[ θ ]
      ⟦ `∀ B ⟧[ θ′ ])
    R
    (interpret W γ θ (N.Λ V))
    (interpret W′ γ′ θ′ (N.Λ V′))
    left-index right-index
indexed-paired-type-abstraction-simulation =
  Proof.indexed-paired-type-abstraction-simulation

module proof.InterpreterIndexedPrimitiveProof where

-- File Charter:
--   * Proves positive-index primitive-term simulation by two indexed chains.
--   * Rebuilds exact operational constant origins after arithmetic.
--   * Uses direct interpreter equations and unary terminal stability only.

open import Agda.Builtin.Equality using (refl)
open import Data.Nat using (_+_)
import Data.Nat
open import Data.Product using (_,_)

open import ImprecisionWf using (idι)
open import Interpreter
open import Core.InterpreterFuel using (interpret-terminal-stable)
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Simulation.Indexed.InterpreterIndexedSimulationMotive
open import Narrowing.InterpreterOperationalValueNarrowing
open import Narrowing.InterpreterOperationalValueNarrowingProperties
open import Typing.InterpreterSemanticTypingCore using
  (base-type; constant-typed)
open import Simulation.Core.InterpreterSimulationContext
open import Simulation.Core.InterpreterSimulationContextProperties
open import Simulation.Core.InterpreterSimulationResult
open import Narrowing.InterpreterTermNarrowing
open import Narrowing.InterpreterTermNarrowingInversion
open import Narrowing.InterpreterTypedValueNarrowing
import NuTermImprecision as NTI
import NuTerms as N
open import Primitives using (addℕ; κℕ)
open import proof.InterpreterIndexedChainSimulation using
  (indexed-chain-simulation)
open import proof.InterpreterIndexedSequenceSimulation using
  (indexed-sequence-simulation)
open import proof.InterpreterIndexedSimulationTransport using
  (indexed-simulation-pointwise)
open import proof.InterpreterPrimitiveSimulationCases using
  (constant-narrowing-injective; natural-value-canonical)
open import proof.InterpreterPrimitiveTermSimulationTail
open import proof.InterpreterSimulationHelpers using
  (fixed-return-simulation)
open import Types

open Narrowing.InterpreterTermNarrowing.RelatedWorlds

operational-primitive-simulation :
  ∀ {W W′ V V′ U U′}
    {R : WorldRelation W W′} →
  OperationalValueNarrowing
    (base-type `ℕ) (base-type `ℕ) R V V′ →
  OperationalValueNarrowing
    (base-type `ℕ) (base-type `ℕ) R U U′ →
  TerminalSimulation
    (OperationalValueResult
      (base-type `ℕ) (base-type `ℕ))
    R
    (fixedOutcome (applyPrimitive W addℕ V U))
    (fixedOutcome (applyPrimitive W′ addℕ V′ U′))
operational-primitive-simulation
    (operational-value
      (typed-value-narrowing V~V′ W⊢ W′⊢ V⊢ V′⊢)
      V-origin)
    (operational-value
      (typed-value-narrowing U~U′ W⊢′ W′⊢′ U⊢ U′⊢)
      U-origin)
    with natural-value-canonical V⊢
       | natural-value-canonical V′⊢
       | natural-value-canonical U⊢
       | natural-value-canonical U′⊢
operational-primitive-simulation
    (operational-value
      (typed-value-narrowing V~V′ W⊢ W′⊢ V⊢ V′⊢)
      V-origin)
    (operational-value
      (typed-value-narrowing U~U′ W⊢′ W′⊢′ U⊢ U′⊢)
      U-origin)
    | m , refl | m′ , refl | n , refl | n′ , refl
    with constant-narrowing-injective V~V′
       | constant-narrowing-injective U~U′
operational-primitive-simulation
    (operational-value
      (typed-value-narrowing V~V′ W⊢ W′⊢ V⊢ V′⊢)
      V-origin)
    (operational-value
      (typed-value-narrowing U~U′ W⊢′ W′⊢′ U⊢ U′⊢)
      U-origin)
    | m , refl | .m , refl | n , refl | .n , refl
    | refl | refl =
  fixed-return-simulation
    (operational-value
      (typed-value-narrowing
        (InterpreterValues.constant⊑ (κℕ (m + n)))
        W⊢ W′⊢ constant-typed constant-typed)
      constant-origin)

indexed-primitive-suc-simulation :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ ρ γᵀ
      θ θ′ γ γ′ L L′ M M′}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  OperationalEnvironmentNarrowing θ θ′ R γᵀ γ γ′ →
  OpenInterpreterTermNarrowing
    R Φ Δᴸ Δᴿ ρ γᵀ
    (L N.⊕[ addℕ ] M)
    (L′ N.⊕[ addℕ ] M′)
    (‵ `ℕ) (‵ `ℕ) idι →
  IndexedInterpreterTermSimulation
    left-index right-index Φ Δᴸ Δᴿ ρ γᵀ
    L L′ (‵ `ℕ) (‵ `ℕ) idι →
  IndexedInterpreterTermSimulation
    left-index right-index Φ Δᴸ Δᴿ ρ γᵀ
    M M′ (‵ `ℕ) (‵ `ℕ) idι →
  IndexedTerminalSimulation
    (OperationalValueResult
      (base-type `ℕ) (base-type `ℕ))
    R
    (interpret W γ θ (L N.⊕[ addℕ ] M))
    (interpret W′ γ′ θ′ (L′ N.⊕[ addℕ ] M′))
    (Data.Nat.suc left-index)
    (Data.Nat.suc right-index)
indexed-primitive-suc-simulation
    {W} {W′} {θ = θ} {θ′} {γ} {γ′}
    {L = L} {L′} {M} {M′}
    {R = R} {runtime = runtime}
    environment origins terms
    left-simulation right-simulation
    with primitive-open-operands terms
indexed-primitive-suc-simulation
    {left-index} {right-index}
    {W} {W′} {θ = θ} {θ′} {γ} {γ′}
    {L = L} {L′} {M} {M′}
    {R = R} {runtime = runtime}
    environment origins terms
    left-simulation right-simulation
    | left-terms , right-terms =
  indexed-simulation-pointwise
    primitive-computation-eq
    primitive-computation-eq
    (indexed-sequence-simulation
      (left-simulation runtime environment origins left-terms)
      tail-simulation
      (λ { {n} {o} terminal eq k →
        interpret-terminal-stable
          {W = W} {γ = γ} {θ = θ} {M = L}
          {n = n} {o = o} terminal eq k
        })
      (λ { {n} {o} terminal eq k →
        interpret-terminal-stable
          {W = W′} {γ = γ′} {θ = θ′} {M = L′}
          {n = n} {o = o} terminal eq k
        })
      (λ U V {n} {o} terminal eq k →
        primitive-tail-stable
          {W = U} {γ = γ} {θ = θ} {M = M} {V = V}
          {n = n} {o = o} terminal eq k)
      (λ U′ V′ {n} {o} terminal eq k →
        primitive-tail-stable
          {W = U′} {γ = γ′} {θ = θ′} {M = M′} {V = V′}
          {n = n} {o = o} terminal eq k))
  where
  tail-simulation :
    ∀ {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    OperationalValueNarrowing
      (base-type `ℕ) (base-type `ℕ) S V V′ →
    IndexedTerminalSimulation
      (OperationalValueResult
        (base-type `ℕ) (base-type `ℕ))
      S
      (primitive-tail U γ θ M V)
      (primitive-tail U′ γ′ θ′ M′ V′)
      left-index right-index
  tail-simulation
      {U = u} {U′ = u′} {V = v} {V′ = v′} {S = relation}
      R≤S V~V′ =
    indexed-chain-simulation
      (right-simulation
        weakened-runtime weakened-environment weakened-origins
        (open-interpreter-narrowing-world-weaken R≤S right-terms))
      (λ S≤T U~U′ →
        terminal-simulation-index
          (operational-primitive-simulation
            (operational-value-narrowing-weaken
              S≤T
              (left-world-typed (operational-typed U~U′))
              (right-world-typed (operational-typed U~U′))
              V~V′)
            U~U′))
      (λ { {n} {o} terminal eq k →
        interpret-terminal-stable
          {W = u} {γ = γ} {θ = θ} {M = M}
          {n = n} {o = o} terminal eq k
        })
      (λ { {n} {o} terminal eq k →
        interpret-terminal-stable
          {W = u′} {γ = γ′} {θ = θ′} {M = M′}
          {n = n} {o = o} terminal eq k
        })
      (primitive-continuation-stable v)
      (primitive-continuation-stable v′)
    where
    weakened-runtime =
      runtime-narrowing-weaken R≤S
        (left-world-typed (operational-typed V~V′))
        (right-world-typed (operational-typed V~V′))
        runtime

    weakened-environment =
      environment-realization-weaken R≤S
        (left-world-typed (operational-typed V~V′))
        (right-world-typed (operational-typed V~V′))
        environment

    weakened-origins =
      operational-environment-narrowing-weaken R≤S
        (left-world-typed (operational-typed V~V′))
        (right-world-typed (operational-typed V~V′))
        origins

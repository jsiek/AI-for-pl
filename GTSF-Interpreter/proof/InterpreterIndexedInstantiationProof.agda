module proof.InterpreterIndexedInstantiationProof where

-- File Charter:
--   * Proves indexed paired and left-only term-instantiation composition.
--   * Keeps operand and post-allocation tail calls at predecessor indices.
--   * Uses direct interpreter equations and unary terminal stability only.

open import Agda.Builtin.Equality using (_≡_; refl)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
import Data.Nat
open import Data.Product using (_,_)

open import Interpreter
open import Core.InterpreterFuel using (interpret-terminal-stable)
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Simulation.Indexed.InterpreterIndexedSimulationMotive
open import Narrowing.InterpreterOperationalValueNarrowing
open import Typing.InterpreterSemanticTypingCore using (⟦_⟧[_])
open import Simulation.Core.InterpreterSimulationContext
open import Simulation.Core.InterpreterSimulationResult using (immediateReturn)
open import Narrowing.InterpreterTermNarrowing
open import Narrowing.InterpreterTermNarrowingInversion
import NuTerms as N
open import proof.InterpreterIndexedOneSidedSequenceSimulation using
  (indexed-left-sequence-simulation)
open import proof.InterpreterIndexedSequenceSimulation using
  (indexed-sequence-simulation)
open import proof.InterpreterIndexedSimulationTransport using
  (indexed-simulation-pointwise)
open import proof.InterpreterInstantiationTail
open import Types

open Narrowing.InterpreterTermNarrowing.RelatedWorlds

indexed-paired-instantiation-suc-simulation :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ ρ γᵀ
      θ θ′ γ γ′ A A′ L L′ c c′ B B′ p}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  OperationalEnvironmentNarrowing θ θ′ R γᵀ γ γ′ →
  (terms :
    OpenInterpreterTermNarrowing
      R Φ Δᴸ Δᴿ ρ γᵀ
      (N.ν A L c) (N.ν A′ L′ c′) B B′ p) →
  aligned-term-root (term-alignment terms) ≡
    paired-instantiation-rootᴬ →
  (∀ {C C′}
      {q : Φ ∣ Δᴸ ⊢ `∀ C ⊑ `∀ C′ ⊣ Δᴿ} →
    IndexedInterpreterTermSimulation
      left-index right-index Φ Δᴸ Δᴿ ρ γᵀ
      L L′ (`∀ C) (`∀ C′) q) →
  (∀ {C C′}
      {q : Φ ∣ Δᴸ ⊢ `∀ C ⊑ `∀ C′ ⊣ Δᴿ}
      {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    OperationalValueNarrowing
      ⟦ `∀ C ⟧[ θ ] ⟦ `∀ C′ ⟧[ θ′ ] S V V′ →
    IndexedTerminalSimulation
      (OperationalValueResult
        ⟦ B ⟧[ θ ] ⟦ B′ ⟧[ θ′ ])
      S
      (instantiation-tail U θ A c V)
      (instantiation-tail U′ θ′ A′ c′ V′)
      left-index right-index) →
  IndexedTerminalSimulation
    (OperationalValueResult
      ⟦ B ⟧[ θ ] ⟦ B′ ⟧[ θ′ ])
    R
    (interpret W γ θ (N.ν A L c))
    (interpret W′ γ′ θ′ (N.ν A′ L′ c′))
    (Data.Nat.suc left-index)
    (Data.Nat.suc right-index)
indexed-paired-instantiation-suc-simulation
    {W = W} {W′} {θ = θ} {θ′} {γ} {γ′}
    {A = A} {A′} {L} {L′} {c} {c′}
    {R = R} {runtime = runtime}
    environment origins terms paired-root
    operand-simulation tail-simulation
    with paired-instantiation-open-body terms paired-root
indexed-paired-instantiation-suc-simulation
    {left-index} {right-index}
    {W = W} {W′} {θ = θ} {θ′} {γ} {γ′}
    {A = A} {A′} {L} {L′} {c} {c′}
    {R = R} {runtime = runtime}
    environment origins terms paired-root
    operand-simulation tail-simulation
    | C , C′ , q , operand-terms =
  indexed-simulation-pointwise
    instantiation-computation-eq
    instantiation-computation-eq
    (indexed-sequence-simulation
      (operand-simulation
        runtime environment origins operand-terms)
      (λ R≤S V~V′ →
        tail-simulation {C = C} {C′ = C′} {q = q}
          R≤S V~V′)
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
        instantiation-tail-stable
          {W = U} {θ = θ} {A = A} {c = c} {V = V}
          {n = n} {o = o} terminal eq k)
      (λ U′ V′ {n} {o} terminal eq k →
        instantiation-tail-stable
          {W = U′} {θ = θ′} {A = A′} {c = c′} {V = V′}
          {n = n} {o = o} terminal eq k))

indexed-left-instantiation-suc-simulation :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ ρ γᵀ
      θ θ′ γ γ′ A L c N′ B B′ p}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  OperationalEnvironmentNarrowing θ θ′ R γᵀ γ γ′ →
  (terms :
    OpenInterpreterTermNarrowing
      R Φ Δᴸ Δᴿ ρ γᵀ
      (N.ν A L c) N′ B B′ p) →
  aligned-term-root (term-alignment terms) ≡
    left-instantiation-rootᴬ →
  (∀ {C}
      {q : Φ ∣ Δᴸ ⊢ `∀ C ⊑ B′ ⊣ Δᴿ} →
    IndexedInterpreterTermSimulation
      left-index right-index Φ Δᴸ Δᴿ ρ γᵀ
      L N′ (`∀ C) B′ q) →
  (∀ {C}
      {q : Φ ∣ Δᴸ ⊢ `∀ C ⊑ B′ ⊣ Δᴿ}
      {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    OperationalValueNarrowing
      ⟦ `∀ C ⟧[ θ ] ⟦ B′ ⟧[ θ′ ] S V V′ →
    IndexedTerminalSimulation
      (OperationalValueResult
        ⟦ B ⟧[ θ ] ⟦ B′ ⟧[ θ′ ])
      S
      (instantiation-tail U θ A c V)
      (immediateReturn U′ V′)
      left-index right-index) →
  IndexedTerminalSimulation
    (OperationalValueResult
      ⟦ B ⟧[ θ ] ⟦ B′ ⟧[ θ′ ])
    R
    (interpret W γ θ (N.ν A L c))
    (interpret W′ γ′ θ′ N′)
    (Data.Nat.suc left-index)
    right-index
indexed-left-instantiation-suc-simulation
    {W = W} {W′} {θ = θ} {θ′} {γ} {γ′}
    {A = A} {L} {c} {N′}
    {R = R} {runtime = runtime}
    environment origins terms left-root
    operand-simulation tail-simulation
    with left-instantiation-open-body terms left-root
indexed-left-instantiation-suc-simulation
    {left-index} {right-index}
    {W = W} {W′} {θ = θ} {θ′} {γ} {γ′}
    {A = A} {L} {c} {N′}
    {R = R} {runtime = runtime}
    environment origins terms left-root
    operand-simulation tail-simulation
    | C , q , operand-terms =
  indexed-simulation-pointwise
    instantiation-computation-eq
    (λ n → refl)
    (indexed-left-sequence-simulation
      (operand-simulation
        runtime environment origins operand-terms)
      (λ R≤S V~V′ →
        tail-simulation {C = C} {q = q} R≤S V~V′)
      (λ { {n} {o} terminal eq k →
        interpret-terminal-stable
          {W = W} {γ = γ} {θ = θ} {M = L}
          {n = n} {o = o} terminal eq k
        })
      (λ U V {n} {o} terminal eq k →
        instantiation-tail-stable
          {W = U} {θ = θ} {A = A} {c = c} {V = V}
          {n = n} {o = o} terminal eq k)
      refl)

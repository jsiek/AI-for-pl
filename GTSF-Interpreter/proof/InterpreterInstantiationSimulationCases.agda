module proof.InterpreterInstantiationSimulationCases where

-- File Charter:
--   * Composes paired polymorphic-operand and instantiation-tail simulations.
--   * Requires explicit evidence that the aligned static root is genuinely
--     paired, excluding syntactically coincident left-only instantiation.
--   * Uses direct interpreter equations only; no reduction semantics occur.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (trans)

open import ImprecisionWf using
  (_∣_⊢_⊑_⊣_)
open import Interpreter
open import Typing.InterpreterErrorFreedom using
  (outcome-typing-excludes-error)
open import Typing.InterpreterSemanticTypingCore using (⟦_⟧[_])
open import Simulation.Core.InterpreterSimulationContext
open import Simulation.Core.InterpreterSimulationResult
open import Narrowing.InterpreterTermNarrowing
open import Narrowing.InterpreterTermNarrowingInversion
open import Simulation.Core.InterpreterTermSimulationMotive
open import Simulation.Core.InterpreterTermSimulationTyping
open import Narrowing.InterpreterTypedValueNarrowing
import NuTerms as N
open import proof.InterpreterInstantiationTail
open import proof.InterpreterOneSidedSequenceSimulation using
  (left-sequence-simulation)
open import proof.InterpreterSequenceSimulation using
  (sequence-simulation)
open import proof.InterpreterSimulationTransport using
  (simulation-pointwise)
open import Types

open Narrowing.InterpreterTermNarrowing.RelatedWorlds

paired-instantiation-term-simulation :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ γᵀ θ θ′ γ γ′
      A A′ L L′ c c′ B B′ p}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  (terms :
    OpenInterpreterTermNarrowing
      R Φ Δᴸ Δᴿ ρ γᵀ
      (N.ν A L c) (N.ν A′ L′ c′) B B′ p) →
  aligned-term-root (term-alignment terms) ≡
    paired-instantiation-rootᴬ →
  (∀ {C C′}
      {q : Φ ∣ Δᴸ ⊢ `∀ C ⊑ `∀ C′ ⊣ Δᴿ} →
    InterpreterTermSimulation
      Φ Δᴸ Δᴿ ρ γᵀ L L′ (`∀ C) (`∀ C′) q) →
  (∀ {C C′}
      {q : Φ ∣ Δᴸ ⊢ `∀ C ⊑ `∀ C′ ⊣ Δᴿ}
      {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    TypedValueNarrowing
      ⟦ `∀ C ⟧[ θ ] ⟦ `∀ C′ ⟧[ θ′ ] S V V′ →
    TerminalSimulation
      (TypedValueResult ⟦ B ⟧[ θ ] ⟦ B′ ⟧[ θ′ ])
      S
      (instantiation-tail U θ A c V)
      (instantiation-tail U′ θ′ A′ c′ V′)) →
  TerminalSimulation
    (TypedValueResult ⟦ B ⟧[ θ ] ⟦ B′ ⟧[ θ′ ])
    R
    (interpret W γ θ (N.ν A L c))
    (interpret W′ γ′ θ′ (N.ν A′ L′ c′))
paired-instantiation-term-simulation
    {W} {W′} {Φ} {Δᴸ} {Δᴿ} {ρ} {γᵀ}
    {θ} {θ′} {γ} {γ′}
    {A} {A′} {L} {L′} {c} {c′}
    {R = R} {runtime = runtime}
    environment terms paired-root
    L-simulation tail-simulation
    with paired-instantiation-open-body terms paired-root
paired-instantiation-term-simulation
    {W} {W′} {Φ} {Δᴸ} {Δᴿ} {ρ} {γᵀ}
    {θ} {θ′} {γ} {γ′}
    {A} {A′} {L} {L′} {c} {c′}
    {R = R} {runtime = runtime}
    environment terms paired-root
    L-simulation tail-simulation
    | C , C′ , q , L-terms =
  simulation-pointwise
    instantiation-computation-eq
    instantiation-computation-eq
    (sequence-simulation
      {W = W} {W′ = W′} {R = R}
      {left-head = interpret W γ θ L}
      {right-head = interpret W′ γ′ θ′ L′}
      {left-continuation =
        λ U V → instantiation-tail U θ A c V}
      {right-continuation =
        λ U′ V′ → instantiation-tail U′ θ′ A′ c′ V′}
      (L-simulation runtime environment L-terms)
      (λ R≤S V~V′ →
        tail-simulation {C = C} {C′ = C′} {q = q}
          R≤S V~V′)
      (λ U V {n} {o} terminal eq k →
        instantiation-tail-stable
          {W = U} {θ = θ} {A = A} {c = c} {V = V}
          {n = n} {o = o} terminal eq k)
      (λ U′ V′ {n} {o} terminal eq k →
        instantiation-tail-stable
          {W = U′} {θ = θ′} {A = A′} {c = c′} {V = V′}
          {n = n} {o = o} terminal eq k)
      (λ { {n} eq →
        outcome-typing-excludes-error
          (target-interpret-typing environment terms n)
          (trans (instantiation-computation-eq n) eq)
        }))

left-instantiation-term-simulation :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ γᵀ θ θ′ γ γ′
      A L c N′ B B′ p}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  (terms :
    OpenInterpreterTermNarrowing
      R Φ Δᴸ Δᴿ ρ γᵀ
      (N.ν A L c) N′ B B′ p) →
  aligned-term-root (term-alignment terms) ≡
    left-instantiation-rootᴬ →
  (∀ {C}
      {q : Φ ∣ Δᴸ ⊢ `∀ C ⊑ B′ ⊣ Δᴿ} →
    InterpreterTermSimulation
      Φ Δᴸ Δᴿ ρ γᵀ L N′ (`∀ C) B′ q) →
  (∀ {C}
      {q : Φ ∣ Δᴸ ⊢ `∀ C ⊑ B′ ⊣ Δᴿ}
      {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    TypedValueNarrowing
      ⟦ `∀ C ⟧[ θ ] ⟦ B′ ⟧[ θ′ ] S V V′ →
    TerminalSimulation
      (TypedValueResult ⟦ B ⟧[ θ ] ⟦ B′ ⟧[ θ′ ])
      S
      (instantiation-tail U θ A c V)
      (immediateReturn U′ V′)) →
  TerminalSimulation
    (TypedValueResult ⟦ B ⟧[ θ ] ⟦ B′ ⟧[ θ′ ])
    R
    (interpret W γ θ (N.ν A L c))
    (interpret W′ γ′ θ′ N′)
left-instantiation-term-simulation
    {W} {W′} {Φ} {Δᴸ} {Δᴿ} {ρ} {γᵀ}
    {θ} {θ′} {γ} {γ′} {A} {L} {c} {N′}
    {R = R} {runtime = runtime}
    environment terms left-root
    L-simulation tail-simulation
    with left-instantiation-open-body terms left-root
left-instantiation-term-simulation
    {W} {W′} {Φ} {Δᴸ} {Δᴿ} {ρ} {γᵀ}
    {θ} {θ′} {γ} {γ′} {A} {L} {c} {N′}
    {R = R} {runtime = runtime}
    environment terms left-root
    L-simulation tail-simulation
    | C , q , L-terms =
  simulation-pointwise
    instantiation-computation-eq
    (λ n → refl)
    (left-sequence-simulation
      {W = W} {W′ = W′} {R = R}
      {left-head = interpret W γ θ L}
      {right-head = interpret W′ γ′ θ′ N′}
      {left-continuation =
        λ U V → instantiation-tail U θ A c V}
      (L-simulation runtime environment L-terms)
      (λ R≤S V~V′ →
        tail-simulation {C = C} {q = q} R≤S V~V′)
      (λ U V {n} {o} terminal eq k →
        instantiation-tail-stable
          {W = U} {θ = θ} {A = A} {c = c} {V = V}
          {n = n} {o = o} terminal eq k))

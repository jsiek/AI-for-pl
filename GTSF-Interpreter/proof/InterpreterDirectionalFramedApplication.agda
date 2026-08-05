module proof.InterpreterDirectionalFramedApplication where

-- File Charter:
--   * Lifts directional application composition to exact framed results.
--   * Erases recursive framed operands only at the operational application
--     boundary and restores the ambient runtime frame on every return.
--   * Contains no interpreter recursion, reduction, or catch-up theorem.

open import Data.Nat using (suc)
open import ImprecisionWf using (_↦_; _∣_⊢_⊑_⊣_)

open import Interpreter
open import Simulation.Directional.InterpreterDirectionalSimulationMotive
open import Narrowing.InterpreterFramedValueNarrowing
open import Narrowing.InterpreterFramedValueNarrowingProperties using
  (framed-environment-operational)
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Narrowing.InterpreterOperationalValueNarrowing
open import Simulation.Core.InterpreterSimulationContext
open import Narrowing.InterpreterTermNarrowing
import NuTerms as N
open import proof.InterpreterDirectionalApplication using
  ( directional-application-backward
  ; directional-application-forward
  ; directional-application-target-blame
  )
open import proof.InterpreterDirectionalFraming using
  ( framed-term-backward-to-operational
  ; framed-term-forward-to-operational
  ; framed-term-target-blame-to-operational
  ; operational-backward-to-framed
  ; operational-forward-to-framed
  )
open import
  proof.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import Types

open Narrowing.InterpreterTermNarrowing.RelatedWorlds

directional-framed-application-forward :
  ∀ {index W W′ Φ Δᴸ Δᴿ ρ γᵀ
      θ θ′ γ γ′ L L′ M M′ B B′ pB}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  AssumptionMembershipUnique Φ →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  FramedEnvironmentNarrowing runtime γᵀ γ γ′ →
  OpenInterpreterTermNarrowing
    R Φ Δᴸ Δᴿ ρ γᵀ
    (L N.· M) (L′ N.· M′) B B′ pB →
  (∀ {A A′}
      {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
    FramedDirectionalInterpreterTermSimulation
      forward-direction index Φ Δᴸ Δᴿ ρ γᵀ
      L L′ (A ⇒ B) (A′ ⇒ B′) (pA ↦ pB)) →
  (∀ {A A′}
      {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
    FramedDirectionalInterpreterTermSimulation
      forward-direction index Φ Δᴸ Δᴿ ρ γᵀ
      M M′ A A′ pA) →
  DirectionalApplyValueSimulation forward-direction index →
  ForwardReturnSimulation
    (FramedValueResult ρ θ θ′ pB) R
    (interpret W γ θ (L N.· M))
    (interpret W′ γ′ θ′ (L′ N.· M′))
    (suc index)
directional-framed-application-forward
    {index} {W} {W′} {Φ} {Δᴸ} {Δᴿ} {ρ} {γᵀ}
    {θ} {θ′} {γ} {γ′} {L} {L′} {M} {M′}
    {B} {B′} {pB} {R} {runtime}
    unique environment origins terms function argument application =
  operational-forward-to-framed
    {W = W} {W′ = W′} {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {left-index = suc index} {ρ = ρ} {θ = θ} {θ′ = θ′}
    {A = B} {A′ = B′} {p = pB} {R = R}
    {left = interpret W γ θ (L N.· M)}
    {right = interpret W′ γ′ θ′ (L′ N.· M′)}
    runtime
    (directional-application-forward
      {index = index} {W = W} {W′ = W′}
      {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      {ρ = ρ} {γᵀ = γᵀ} {θ = θ} {θ′ = θ′}
      {γ = γ} {γ′ = γ′} {L = L} {L′ = L′}
      {M = M} {M′ = M′} {B = B} {B′ = B′}
      {pB = pB} {R = R} {runtime = runtime}
      environment (framed-environment-operational origins) terms
      (λ {A} {A′} {pA} →
        framed-term-forward-to-operational
          {index = index} {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
          {ρ = ρ} {γᵀ = γᵀ} {N = L} {N′ = L′}
          {A = A ⇒ B} {A′ = A′ ⇒ B′} {p = pA ↦ pB}
          (function {A = A} {A′ = A′} {pA = pA}) unique)
      (λ {A} {A′} {pA} →
        framed-term-forward-to-operational
          {index = index} {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
          {ρ = ρ} {γᵀ = γᵀ} {N = M} {N′ = M′}
          {A = A} {A′ = A′} {p = pA}
          (argument {A = A} {A′ = A′} {pA = pA}) unique)
      application)

directional-framed-application-backward :
  ∀ {index W W′ Φ Δᴸ Δᴿ ρ γᵀ
      θ θ′ γ γ′ L L′ M M′ B B′ pB}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  AssumptionMembershipUnique Φ →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  FramedEnvironmentNarrowing runtime γᵀ γ γ′ →
  OpenInterpreterTermNarrowing
    R Φ Δᴸ Δᴿ ρ γᵀ
    (L N.· M) (L′ N.· M′) B B′ pB →
  (∀ {A A′}
      {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
    FramedDirectionalInterpreterTermSimulation
      backward-direction index Φ Δᴸ Δᴿ ρ γᵀ
      L L′ (A ⇒ B) (A′ ⇒ B′) (pA ↦ pB)) →
  (∀ {A A′}
      {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
    FramedDirectionalInterpreterTermSimulation
      target-blame-direction index Φ Δᴸ Δᴿ ρ γᵀ
      L L′ (A ⇒ B) (A′ ⇒ B′) (pA ↦ pB)) →
  (∀ {A A′}
      {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
    FramedDirectionalInterpreterTermSimulation
      backward-direction index Φ Δᴸ Δᴿ ρ γᵀ
      M M′ A A′ pA) →
  (∀ {A A′}
      {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
    FramedDirectionalInterpreterTermSimulation
      target-blame-direction index Φ Δᴸ Δᴿ ρ γᵀ
      M M′ A A′ pA) →
  DirectionalApplyValueSimulation backward-direction index →
  DirectionalApplyValueSimulation target-blame-direction index →
  BackwardReturnSimulation
    (FramedValueResult ρ θ θ′ pB) R
    (interpret W γ θ (L N.· M))
    (interpret W′ γ′ θ′ (L′ N.· M′))
    (suc index)
directional-framed-application-backward
    {index} {W} {W′} {Φ} {Δᴸ} {Δᴿ} {ρ} {γᵀ}
    {θ} {θ′} {γ} {γ′} {L} {L′} {M} {M′}
    {B} {B′} {pB} {R} {runtime}
    unique environment origins terms
    function-backward function-blame
    argument-backward argument-blame
    application-backward application-blame =
  operational-backward-to-framed
    {W = W} {W′ = W′} {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {right-index = suc index} {ρ = ρ} {θ = θ} {θ′ = θ′}
    {A = B} {A′ = B′} {p = pB} {R = R}
    {left = interpret W γ θ (L N.· M)}
    {right = interpret W′ γ′ θ′ (L′ N.· M′)}
    runtime
    (directional-application-backward
      {index = index} {W = W} {W′ = W′}
      {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      {ρ = ρ} {γᵀ = γᵀ} {θ = θ} {θ′ = θ′}
      {γ = γ} {γ′ = γ′} {L = L} {L′ = L′}
      {M = M} {M′ = M′} {B = B} {B′ = B′}
      {pB = pB} {R = R} {runtime = runtime}
      environment (framed-environment-operational origins) terms
      (λ {A} {A′} {pA} →
        framed-term-backward-to-operational
          {index = index} {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
          {ρ = ρ} {γᵀ = γᵀ} {N = L} {N′ = L′}
          {A = A ⇒ B} {A′ = A′ ⇒ B′} {p = pA ↦ pB}
          unique
          (function-backward
            {A = A} {A′ = A′} {pA = pA}))
      (λ {A} {A′} {pA} →
        framed-term-target-blame-to-operational
          {index = index} {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
          {ρ = ρ} {γᵀ = γᵀ} {N = L} {N′ = L′}
          {A = A ⇒ B} {A′ = A′ ⇒ B′} {p = pA ↦ pB}
          unique
          (function-blame
            {A = A} {A′ = A′} {pA = pA}))
      (λ {A} {A′} {pA} →
        framed-term-backward-to-operational
          {index = index} {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
          {ρ = ρ} {γᵀ = γᵀ} {N = M} {N′ = M′}
          {A = A} {A′ = A′} {p = pA}
          unique
          (argument-backward
            {A = A} {A′ = A′} {pA = pA}))
      (λ {A} {A′} {pA} →
        framed-term-target-blame-to-operational
          {index = index} {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
          {ρ = ρ} {γᵀ = γᵀ} {N = M} {N′ = M′}
          {A = A} {A′ = A′} {p = pA}
          unique
          (argument-blame
            {A = A} {A′ = A′} {pA = pA}))
      application-backward application-blame)

directional-framed-application-target-blame :
  ∀ {index W W′ Φ Δᴸ Δᴿ ρ γᵀ
      θ θ′ γ γ′ L L′ M M′ B B′ pB}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  AssumptionMembershipUnique Φ →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  FramedEnvironmentNarrowing runtime γᵀ γ γ′ →
  OpenInterpreterTermNarrowing
    R Φ Δᴸ Δᴿ ρ γᵀ
    (L N.· M) (L′ N.· M′) B B′ pB →
  (∀ {A A′}
      {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
    FramedDirectionalInterpreterTermSimulation
      backward-direction index Φ Δᴸ Δᴿ ρ γᵀ
      L L′ (A ⇒ B) (A′ ⇒ B′) (pA ↦ pB)) →
  (∀ {A A′}
      {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
    FramedDirectionalInterpreterTermSimulation
      target-blame-direction index Φ Δᴸ Δᴿ ρ γᵀ
      L L′ (A ⇒ B) (A′ ⇒ B′) (pA ↦ pB)) →
  (∀ {A A′}
      {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
    FramedDirectionalInterpreterTermSimulation
      backward-direction index Φ Δᴸ Δᴿ ρ γᵀ
      M M′ A A′ pA) →
  (∀ {A A′}
      {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
    FramedDirectionalInterpreterTermSimulation
      target-blame-direction index Φ Δᴸ Δᴿ ρ γᵀ
      M M′ A A′ pA) →
  DirectionalApplyValueSimulation backward-direction index →
  DirectionalApplyValueSimulation target-blame-direction index →
  TargetBlameSimulation R
    (interpret W γ θ (L N.· M))
    (interpret W′ γ′ θ′ (L′ N.· M′))
    (suc index)
directional-framed-application-target-blame
    {index} {W} {W′} {Φ} {Δᴸ} {Δᴿ} {ρ} {γᵀ}
    {θ} {θ′} {γ} {γ′} {L} {L′} {M} {M′}
    {B} {B′} {pB} {R} {runtime}
    unique environment origins terms
    function-backward function-blame
    argument-backward argument-blame
    application-backward application-blame =
  directional-application-target-blame
    {index = index} {W = W} {W′ = W′}
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {ρ = ρ} {γᵀ = γᵀ} {θ = θ} {θ′ = θ′}
    {γ = γ} {γ′ = γ′} {L = L} {L′ = L′}
    {M = M} {M′ = M′} {B = B} {B′ = B′}
    {pB = pB} {R = R} {runtime = runtime}
    environment (framed-environment-operational origins) terms
    (λ {A} {A′} {pA} →
      framed-term-backward-to-operational
        {index = index} {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
        {ρ = ρ} {γᵀ = γᵀ} {N = L} {N′ = L′}
        {A = A ⇒ B} {A′ = A′ ⇒ B′} {p = pA ↦ pB}
        unique
        (function-backward
          {A = A} {A′ = A′} {pA = pA}))
    (λ {A} {A′} {pA} →
      framed-term-target-blame-to-operational
        {index = index} {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
        {ρ = ρ} {γᵀ = γᵀ} {N = L} {N′ = L′}
        {A = A ⇒ B} {A′ = A′ ⇒ B′} {p = pA ↦ pB}
        unique
        (function-blame
          {A = A} {A′ = A′} {pA = pA}))
    (λ {A} {A′} {pA} →
      framed-term-backward-to-operational
        {index = index} {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
        {ρ = ρ} {γᵀ = γᵀ} {N = M} {N′ = M′}
        {A = A} {A′ = A′} {p = pA}
        unique
        (argument-backward
          {A = A} {A′ = A′} {pA = pA}))
    (λ {A} {A′} {pA} →
      framed-term-target-blame-to-operational
        {index = index} {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
        {ρ = ρ} {γᵀ = γᵀ} {N = M} {N′ = M′}
        {A = A} {A′ = A′} {p = pA}
        unique
        (argument-blame
          {A = A} {A′ = A′} {pA = pA}))
    application-backward application-blame

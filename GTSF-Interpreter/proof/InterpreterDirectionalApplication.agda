module proof.InterpreterDirectionalApplication where

-- File Charter:
--   * Derives the three positive-fuel application observations from
--     direction-specific recursive function, argument, and `applyValue`
--     simulations.
--   * Reuses the checked compositional application proof by filling the
--     unused endpoint only at fuel zero.
--   * Contains no interpreter recursion, reduction, or catch-up theorem.

open import ImprecisionWf using
  (_↦_; _∣_⊢_⊑_⊣_)
open import Data.Nat using (suc; zero)
open import Relation.Binary.PropositionalEquality using (refl)

open import Interpreter
open import Simulation.Directional.InterpreterDirectionalSimulationMotive
open import Simulation.Indexed.InterpreterIndexedApplication
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Simulation.Indexed.InterpreterIndexedSimulationMotive
open import Narrowing.InterpreterOperationalValueNarrowing
open import Typing.InterpreterSemanticTypingCore using (⟦_⟧[_])
open import Simulation.Core.InterpreterSimulationContext
open import Narrowing.InterpreterTermNarrowing
import NuTerms as N
open import proof.InterpreterDirectionalSimulation using
  (backward-at-left-zero; forward-at-right-zero)
open import Types

open Narrowing.InterpreterTermNarrowing.RelatedWorlds

directional-application-forward :
  ∀ {index W W′ Φ Δᴸ Δᴿ ρ γᵀ
      θ θ′ γ γ′ L L′ M M′ B B′ pB}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  OperationalEnvironmentNarrowing θ θ′ R γᵀ γ γ′ →
  OpenInterpreterTermNarrowing
    R Φ Δᴸ Δᴿ ρ γᵀ
    (L N.· M) (L′ N.· M′) B B′ pB →
  (∀ {A A′}
      {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
    DirectionalInterpreterTermSimulation
      forward-direction index Φ Δᴸ Δᴿ ρ γᵀ
      L L′ (A ⇒ B) (A′ ⇒ B′) (pA ↦ pB)) →
  (∀ {A A′}
      {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
    DirectionalInterpreterTermSimulation
      forward-direction index Φ Δᴸ Δᴿ ρ γᵀ
      M M′ A A′ pA) →
  DirectionalApplyValueSimulation forward-direction index →
  ForwardReturnSimulation
    (OperationalValueResult
      ⟦ B ⟧[ θ ] ⟦ B′ ⟧[ θ′ ])
    R
    (interpret W γ θ (L N.· M))
    (interpret W′ γ′ θ′ (L′ N.· M′))
    (suc index)
directional-application-forward
    {index} {runtime = runtime}
    environment origins terms
    function-simulation argument-simulation apply-simulation =
  forward-return
    (indexed-application-suc-simulation
      {left-index = index} {right-index = zero}
      environment origins terms
      (λ runtime₀ environment₀ origins₀ terms₀ →
        forward-at-right-zero refl
          (function-simulation
            runtime₀ environment₀ origins₀ terms₀))
      (λ runtime₀ environment₀ origins₀ terms₀ →
        forward-at-right-zero refl
          (argument-simulation
            runtime₀ environment₀ origins₀ terms₀))
      (λ value argument →
        forward-at-right-zero refl
          (apply-simulation value argument)))

directional-application-backward :
  ∀ {index W W′ Φ Δᴸ Δᴿ ρ γᵀ
      θ θ′ γ γ′ L L′ M M′ B B′ pB}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  OperationalEnvironmentNarrowing θ θ′ R γᵀ γ γ′ →
  OpenInterpreterTermNarrowing
    R Φ Δᴸ Δᴿ ρ γᵀ
    (L N.· M) (L′ N.· M′) B B′ pB →
  (∀ {A A′}
      {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
    DirectionalInterpreterTermSimulation
      backward-direction index Φ Δᴸ Δᴿ ρ γᵀ
      L L′ (A ⇒ B) (A′ ⇒ B′) (pA ↦ pB)) →
  (∀ {A A′}
      {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
    DirectionalInterpreterTermSimulation
      target-blame-direction index Φ Δᴸ Δᴿ ρ γᵀ
      L L′ (A ⇒ B) (A′ ⇒ B′) (pA ↦ pB)) →
  (∀ {A A′}
      {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
    DirectionalInterpreterTermSimulation
      backward-direction index Φ Δᴸ Δᴿ ρ γᵀ
      M M′ A A′ pA) →
  (∀ {A A′}
      {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
    DirectionalInterpreterTermSimulation
      target-blame-direction index Φ Δᴸ Δᴿ ρ γᵀ
      M M′ A A′ pA) →
  DirectionalApplyValueSimulation backward-direction index →
  DirectionalApplyValueSimulation target-blame-direction index →
  BackwardReturnSimulation
    (OperationalValueResult
      ⟦ B ⟧[ θ ] ⟦ B′ ⟧[ θ′ ])
    R
    (interpret W γ θ (L N.· M))
    (interpret W′ γ′ θ′ (L′ N.· M′))
    (suc index)
directional-application-backward
    {index}
    environment origins terms
    function-backward function-blame
    argument-backward argument-blame
    apply-backward apply-blame =
  backward-return
    (indexed-application-suc-simulation
      {left-index = zero} {right-index = index}
      environment origins terms
      (λ runtime₀ environment₀ origins₀ terms₀ →
        backward-at-left-zero refl
          (function-backward
            runtime₀ environment₀ origins₀ terms₀)
          (function-blame
            runtime₀ environment₀ origins₀ terms₀))
      (λ runtime₀ environment₀ origins₀ terms₀ →
        backward-at-left-zero refl
          (argument-backward
            runtime₀ environment₀ origins₀ terms₀)
          (argument-blame
            runtime₀ environment₀ origins₀ terms₀))
      (λ value argument →
        backward-at-left-zero refl
          (apply-backward value argument)
          (apply-blame value argument)))

directional-application-target-blame :
  ∀ {index W W′ Φ Δᴸ Δᴿ ρ γᵀ
      θ θ′ γ γ′ L L′ M M′ B B′ pB}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  OperationalEnvironmentNarrowing θ θ′ R γᵀ γ γ′ →
  OpenInterpreterTermNarrowing
    R Φ Δᴸ Δᴿ ρ γᵀ
    (L N.· M) (L′ N.· M′) B B′ pB →
  (∀ {A A′}
      {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
    DirectionalInterpreterTermSimulation
      backward-direction index Φ Δᴸ Δᴿ ρ γᵀ
      L L′ (A ⇒ B) (A′ ⇒ B′) (pA ↦ pB)) →
  (∀ {A A′}
      {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
    DirectionalInterpreterTermSimulation
      target-blame-direction index Φ Δᴸ Δᴿ ρ γᵀ
      L L′ (A ⇒ B) (A′ ⇒ B′) (pA ↦ pB)) →
  (∀ {A A′}
      {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
    DirectionalInterpreterTermSimulation
      backward-direction index Φ Δᴸ Δᴿ ρ γᵀ
      M M′ A A′ pA) →
  (∀ {A A′}
      {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
    DirectionalInterpreterTermSimulation
      target-blame-direction index Φ Δᴸ Δᴿ ρ γᵀ
      M M′ A A′ pA) →
  DirectionalApplyValueSimulation backward-direction index →
  DirectionalApplyValueSimulation target-blame-direction index →
  TargetBlameSimulation R
    (interpret W γ θ (L N.· M))
    (interpret W′ γ′ θ′ (L′ N.· M′))
    (suc index)
directional-application-target-blame
    {index}
    environment origins terms
    function-backward function-blame
    argument-backward argument-blame
    apply-backward apply-blame =
  target-blame-reflects
    (indexed-application-suc-simulation
      {left-index = zero} {right-index = index}
      environment origins terms
      (λ runtime₀ environment₀ origins₀ terms₀ →
        backward-at-left-zero refl
          (function-backward
            runtime₀ environment₀ origins₀ terms₀)
          (function-blame
            runtime₀ environment₀ origins₀ terms₀))
      (λ runtime₀ environment₀ origins₀ terms₀ →
        backward-at-left-zero refl
          (argument-backward
            runtime₀ environment₀ origins₀ terms₀)
          (argument-blame
            runtime₀ environment₀ origins₀ terms₀))
      (λ value argument →
        backward-at-left-zero refl
          (apply-backward value argument)
          (apply-blame value argument)))

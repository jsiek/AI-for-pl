module proof.InterpreterDirectionalPrimitive where

-- File Charter:
--   * Derives the three positive-fuel primitive observations from
--     direction-specific recursive operand simulations.
--   * Reuses the checked primitive composition proof with the unused
--     endpoint fixed at zero.
--   * Contains no interpreter recursion or reduction theorem.

open import ImprecisionWf using (idι)
open import Data.Nat using (suc; zero)
open import Relation.Binary.PropositionalEquality using (refl)

open import Interpreter
open import Simulation.Directional.InterpreterDirectionalSimulationMotive
open import Simulation.Indexed.InterpreterIndexedPrimitive
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Narrowing.InterpreterOperationalValueNarrowing
open import Typing.InterpreterSemanticTypingCore using (base-type)
open import Simulation.Core.InterpreterSimulationContext
open import Narrowing.InterpreterTermNarrowing
import NuTerms as N
open import Primitives using (addℕ)
open import proof.InterpreterDirectionalSimulation using
  (backward-at-left-zero; forward-at-right-zero)
open import Types

open Narrowing.InterpreterTermNarrowing.RelatedWorlds

directional-primitive-forward :
  ∀ {index W W′ Φ Δᴸ Δᴿ ρ γᵀ θ θ′ γ γ′ L L′ M M′}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  OperationalEnvironmentNarrowing θ θ′ R γᵀ γ γ′ →
  OpenInterpreterTermNarrowing
    R Φ Δᴸ Δᴿ ρ γᵀ
    (L N.⊕[ addℕ ] M) (L′ N.⊕[ addℕ ] M′)
    (‵ `ℕ) (‵ `ℕ) idι →
  DirectionalInterpreterTermSimulation
    forward-direction index Φ Δᴸ Δᴿ ρ γᵀ
    L L′ (‵ `ℕ) (‵ `ℕ) idι →
  DirectionalInterpreterTermSimulation
    forward-direction index Φ Δᴸ Δᴿ ρ γᵀ
    M M′ (‵ `ℕ) (‵ `ℕ) idι →
  ForwardReturnSimulation
    (OperationalValueResult (base-type `ℕ) (base-type `ℕ)) R
    (interpret W γ θ (L N.⊕[ addℕ ] M))
    (interpret W′ γ′ θ′ (L′ N.⊕[ addℕ ] M′))
    (suc index)
directional-primitive-forward
    {index} environment origins terms left right =
  forward-return
    (indexed-primitive-suc-simulation
      {left-index = index} {right-index = zero}
      environment origins terms
      (λ runtime₀ environment₀ origins₀ terms₀ →
        forward-at-right-zero refl
          (left runtime₀ environment₀ origins₀ terms₀))
      (λ runtime₀ environment₀ origins₀ terms₀ →
        forward-at-right-zero refl
          (right runtime₀ environment₀ origins₀ terms₀)))

directional-primitive-backward :
  ∀ {index W W′ Φ Δᴸ Δᴿ ρ γᵀ θ θ′ γ γ′ L L′ M M′}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  OperationalEnvironmentNarrowing θ θ′ R γᵀ γ γ′ →
  OpenInterpreterTermNarrowing
    R Φ Δᴸ Δᴿ ρ γᵀ
    (L N.⊕[ addℕ ] M) (L′ N.⊕[ addℕ ] M′)
    (‵ `ℕ) (‵ `ℕ) idι →
  DirectionalInterpreterTermSimulation
    backward-direction index Φ Δᴸ Δᴿ ρ γᵀ
    L L′ (‵ `ℕ) (‵ `ℕ) idι →
  DirectionalInterpreterTermSimulation
    target-blame-direction index Φ Δᴸ Δᴿ ρ γᵀ
    L L′ (‵ `ℕ) (‵ `ℕ) idι →
  DirectionalInterpreterTermSimulation
    backward-direction index Φ Δᴸ Δᴿ ρ γᵀ
    M M′ (‵ `ℕ) (‵ `ℕ) idι →
  DirectionalInterpreterTermSimulation
    target-blame-direction index Φ Δᴸ Δᴿ ρ γᵀ
    M M′ (‵ `ℕ) (‵ `ℕ) idι →
  BackwardReturnSimulation
    (OperationalValueResult (base-type `ℕ) (base-type `ℕ)) R
    (interpret W γ θ (L N.⊕[ addℕ ] M))
    (interpret W′ γ′ θ′ (L′ N.⊕[ addℕ ] M′))
    (suc index)
directional-primitive-backward
    {index} environment origins terms
    left-backward left-blame right-backward right-blame =
  backward-return
    (indexed-primitive-suc-simulation
      {left-index = zero} {right-index = index}
      environment origins terms
      (λ runtime₀ environment₀ origins₀ terms₀ →
        backward-at-left-zero refl
          (left-backward runtime₀ environment₀ origins₀ terms₀)
          (left-blame runtime₀ environment₀ origins₀ terms₀))
      (λ runtime₀ environment₀ origins₀ terms₀ →
        backward-at-left-zero refl
          (right-backward runtime₀ environment₀ origins₀ terms₀)
          (right-blame runtime₀ environment₀ origins₀ terms₀)))

directional-primitive-target-blame :
  ∀ {index W W′ Φ Δᴸ Δᴿ ρ γᵀ θ θ′ γ γ′ L L′ M M′}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  OperationalEnvironmentNarrowing θ θ′ R γᵀ γ γ′ →
  OpenInterpreterTermNarrowing
    R Φ Δᴸ Δᴿ ρ γᵀ
    (L N.⊕[ addℕ ] M) (L′ N.⊕[ addℕ ] M′)
    (‵ `ℕ) (‵ `ℕ) idι →
  DirectionalInterpreterTermSimulation
    backward-direction index Φ Δᴸ Δᴿ ρ γᵀ
    L L′ (‵ `ℕ) (‵ `ℕ) idι →
  DirectionalInterpreterTermSimulation
    target-blame-direction index Φ Δᴸ Δᴿ ρ γᵀ
    L L′ (‵ `ℕ) (‵ `ℕ) idι →
  DirectionalInterpreterTermSimulation
    backward-direction index Φ Δᴸ Δᴿ ρ γᵀ
    M M′ (‵ `ℕ) (‵ `ℕ) idι →
  DirectionalInterpreterTermSimulation
    target-blame-direction index Φ Δᴸ Δᴿ ρ γᵀ
    M M′ (‵ `ℕ) (‵ `ℕ) idι →
  TargetBlameSimulation R
    (interpret W γ θ (L N.⊕[ addℕ ] M))
    (interpret W′ γ′ θ′ (L′ N.⊕[ addℕ ] M′))
    (suc index)
directional-primitive-target-blame
    {index} environment origins terms
    left-backward left-blame right-backward right-blame =
  target-blame-reflects
    (indexed-primitive-suc-simulation
      {left-index = zero} {right-index = index}
      environment origins terms
      (λ runtime₀ environment₀ origins₀ terms₀ →
        backward-at-left-zero refl
          (left-backward runtime₀ environment₀ origins₀ terms₀)
          (left-blame runtime₀ environment₀ origins₀ terms₀))
      (λ runtime₀ environment₀ origins₀ terms₀ →
        backward-at-left-zero refl
          (right-backward runtime₀ environment₀ origins₀ terms₀)
          (right-blame runtime₀ environment₀ origins₀ terms₀)))

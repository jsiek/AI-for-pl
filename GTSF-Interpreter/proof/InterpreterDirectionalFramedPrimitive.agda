module proof.InterpreterDirectionalFramedPrimitive where

-- File Charter:
--   * Lifts directional natural-addition composition to exact framed
--     results.
--   * Erases recursive operands at the primitive boundary and restores the
--     ambient runtime frame on returned constants.
--   * Contains no interpreter recursion, reduction, or catch-up theorem.

open import Data.Nat using (suc)
open import ImprecisionWf using (idι)

open import Interpreter
open import Simulation.Directional.InterpreterDirectionalSimulationMotive
open import Narrowing.InterpreterFramedValueNarrowing
open import Narrowing.InterpreterFramedValueNarrowingProperties using
  (framed-environment-operational)
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Simulation.Core.InterpreterSimulationContext
open import Narrowing.InterpreterTermNarrowing
import NuTerms as N
open import Primitives using (addℕ)
open import proof.InterpreterDirectionalFraming using
  ( framed-term-backward-to-operational
  ; framed-term-forward-to-operational
  ; framed-term-target-blame-to-operational
  ; operational-backward-to-framed
  ; operational-forward-to-framed
  )
open import proof.InterpreterDirectionalPrimitive using
  ( directional-primitive-backward
  ; directional-primitive-forward
  ; directional-primitive-target-blame
  )
open import
  proof.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import Types

open Narrowing.InterpreterTermNarrowing.RelatedWorlds

directional-framed-primitive-forward :
  ∀ {index W W′ Φ Δᴸ Δᴿ ρ γᵀ
      θ θ′ γ γ′ L L′ M M′}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  AssumptionMembershipUnique Φ →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  FramedEnvironmentNarrowing runtime γᵀ γ γ′ →
  OpenInterpreterTermNarrowing
    R Φ Δᴸ Δᴿ ρ γᵀ
    (L N.⊕[ addℕ ] M) (L′ N.⊕[ addℕ ] M′)
    (‵ `ℕ) (‵ `ℕ) idι →
  FramedDirectionalInterpreterTermSimulation
    forward-direction index Φ Δᴸ Δᴿ ρ γᵀ
    L L′ (‵ `ℕ) (‵ `ℕ) idι →
  FramedDirectionalInterpreterTermSimulation
    forward-direction index Φ Δᴸ Δᴿ ρ γᵀ
    M M′ (‵ `ℕ) (‵ `ℕ) idι →
  ForwardReturnSimulation
    (FramedValueResult ρ θ θ′ idι) R
    (interpret W γ θ (L N.⊕[ addℕ ] M))
    (interpret W′ γ′ θ′ (L′ N.⊕[ addℕ ] M′))
    (suc index)
directional-framed-primitive-forward
    {index} {W} {W′} {Φ} {Δᴸ} {Δᴿ} {ρ} {γᵀ}
    {θ} {θ′} {γ} {γ′} {L} {L′} {M} {M′}
    {R} {runtime}
    unique environment origins terms left right =
  operational-forward-to-framed
    {W = W} {W′ = W′} {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {left-index = suc index} {ρ = ρ} {θ = θ} {θ′ = θ′}
    {A = ‵ `ℕ} {A′ = ‵ `ℕ} {p = idι} {R = R}
    {left = interpret W γ θ (L N.⊕[ addℕ ] M)}
    {right = interpret W′ γ′ θ′ (L′ N.⊕[ addℕ ] M′)}
    runtime
    (directional-primitive-forward
      {index = index} {W = W} {W′ = W′}
      {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      {ρ = ρ} {γᵀ = γᵀ} {θ = θ} {θ′ = θ′}
      {γ = γ} {γ′ = γ′} {L = L} {L′ = L′}
      {M = M} {M′ = M′} {R = R} {runtime = runtime}
      environment (framed-environment-operational origins) terms
      (framed-term-forward-to-operational
        {index = index} {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
        {ρ = ρ} {γᵀ = γᵀ} {N = L} {N′ = L′}
        {A = ‵ `ℕ} {A′ = ‵ `ℕ} {p = idι}
        left unique)
      (framed-term-forward-to-operational
        {index = index} {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
        {ρ = ρ} {γᵀ = γᵀ} {N = M} {N′ = M′}
        {A = ‵ `ℕ} {A′ = ‵ `ℕ} {p = idι}
        right unique))

directional-framed-primitive-backward :
  ∀ {index W W′ Φ Δᴸ Δᴿ ρ γᵀ
      θ θ′ γ γ′ L L′ M M′}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  AssumptionMembershipUnique Φ →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  FramedEnvironmentNarrowing runtime γᵀ γ γ′ →
  OpenInterpreterTermNarrowing
    R Φ Δᴸ Δᴿ ρ γᵀ
    (L N.⊕[ addℕ ] M) (L′ N.⊕[ addℕ ] M′)
    (‵ `ℕ) (‵ `ℕ) idι →
  FramedDirectionalInterpreterTermSimulation
    backward-direction index Φ Δᴸ Δᴿ ρ γᵀ
    L L′ (‵ `ℕ) (‵ `ℕ) idι →
  FramedDirectionalInterpreterTermSimulation
    target-blame-direction index Φ Δᴸ Δᴿ ρ γᵀ
    L L′ (‵ `ℕ) (‵ `ℕ) idι →
  FramedDirectionalInterpreterTermSimulation
    backward-direction index Φ Δᴸ Δᴿ ρ γᵀ
    M M′ (‵ `ℕ) (‵ `ℕ) idι →
  FramedDirectionalInterpreterTermSimulation
    target-blame-direction index Φ Δᴸ Δᴿ ρ γᵀ
    M M′ (‵ `ℕ) (‵ `ℕ) idι →
  BackwardReturnSimulation
    (FramedValueResult ρ θ θ′ idι) R
    (interpret W γ θ (L N.⊕[ addℕ ] M))
    (interpret W′ γ′ θ′ (L′ N.⊕[ addℕ ] M′))
    (suc index)
directional-framed-primitive-backward
    {index} {W} {W′} {Φ} {Δᴸ} {Δᴿ} {ρ} {γᵀ}
    {θ} {θ′} {γ} {γ′} {L} {L′} {M} {M′}
    {R} {runtime}
    unique environment origins terms
    left-backward left-blame right-backward right-blame =
  operational-backward-to-framed
    {W = W} {W′ = W′} {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {right-index = suc index} {ρ = ρ} {θ = θ} {θ′ = θ′}
    {A = ‵ `ℕ} {A′ = ‵ `ℕ} {p = idι} {R = R}
    {left = interpret W γ θ (L N.⊕[ addℕ ] M)}
    {right = interpret W′ γ′ θ′ (L′ N.⊕[ addℕ ] M′)}
    runtime
    (directional-primitive-backward
      {index = index} {W = W} {W′ = W′}
      {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      {ρ = ρ} {γᵀ = γᵀ} {θ = θ} {θ′ = θ′}
      {γ = γ} {γ′ = γ′} {L = L} {L′ = L′}
      {M = M} {M′ = M′} {R = R} {runtime = runtime}
      environment (framed-environment-operational origins) terms
      (framed-term-backward-to-operational
        {index = index} {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
        {ρ = ρ} {γᵀ = γᵀ} {N = L} {N′ = L′}
        {A = ‵ `ℕ} {A′ = ‵ `ℕ} {p = idι}
        unique left-backward)
      (framed-term-target-blame-to-operational
        {index = index} {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
        {ρ = ρ} {γᵀ = γᵀ} {N = L} {N′ = L′}
        {A = ‵ `ℕ} {A′ = ‵ `ℕ} {p = idι}
        unique left-blame)
      (framed-term-backward-to-operational
        {index = index} {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
        {ρ = ρ} {γᵀ = γᵀ} {N = M} {N′ = M′}
        {A = ‵ `ℕ} {A′ = ‵ `ℕ} {p = idι}
        unique right-backward)
      (framed-term-target-blame-to-operational
        {index = index} {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
        {ρ = ρ} {γᵀ = γᵀ} {N = M} {N′ = M′}
        {A = ‵ `ℕ} {A′ = ‵ `ℕ} {p = idι}
        unique right-blame))

directional-framed-primitive-target-blame :
  ∀ {index W W′ Φ Δᴸ Δᴿ ρ γᵀ
      θ θ′ γ γ′ L L′ M M′}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  AssumptionMembershipUnique Φ →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  FramedEnvironmentNarrowing runtime γᵀ γ γ′ →
  OpenInterpreterTermNarrowing
    R Φ Δᴸ Δᴿ ρ γᵀ
    (L N.⊕[ addℕ ] M) (L′ N.⊕[ addℕ ] M′)
    (‵ `ℕ) (‵ `ℕ) idι →
  FramedDirectionalInterpreterTermSimulation
    backward-direction index Φ Δᴸ Δᴿ ρ γᵀ
    L L′ (‵ `ℕ) (‵ `ℕ) idι →
  FramedDirectionalInterpreterTermSimulation
    target-blame-direction index Φ Δᴸ Δᴿ ρ γᵀ
    L L′ (‵ `ℕ) (‵ `ℕ) idι →
  FramedDirectionalInterpreterTermSimulation
    backward-direction index Φ Δᴸ Δᴿ ρ γᵀ
    M M′ (‵ `ℕ) (‵ `ℕ) idι →
  FramedDirectionalInterpreterTermSimulation
    target-blame-direction index Φ Δᴸ Δᴿ ρ γᵀ
    M M′ (‵ `ℕ) (‵ `ℕ) idι →
  TargetBlameSimulation R
    (interpret W γ θ (L N.⊕[ addℕ ] M))
    (interpret W′ γ′ θ′ (L′ N.⊕[ addℕ ] M′))
    (suc index)
directional-framed-primitive-target-blame
    {index} {W} {W′} {Φ} {Δᴸ} {Δᴿ} {ρ} {γᵀ}
    {θ} {θ′} {γ} {γ′} {L} {L′} {M} {M′}
    {R} {runtime}
    unique environment origins terms
    left-backward left-blame right-backward right-blame =
  directional-primitive-target-blame
    {index = index} {W = W} {W′ = W′}
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {ρ = ρ} {γᵀ = γᵀ} {θ = θ} {θ′ = θ′}
    {γ = γ} {γ′ = γ′} {L = L} {L′ = L′}
    {M = M} {M′ = M′} {R = R} {runtime = runtime}
    environment (framed-environment-operational origins) terms
    (framed-term-backward-to-operational
      {index = index} {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      {ρ = ρ} {γᵀ = γᵀ} {N = L} {N′ = L′}
      {A = ‵ `ℕ} {A′ = ‵ `ℕ} {p = idι}
      unique left-backward)
    (framed-term-target-blame-to-operational
      {index = index} {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      {ρ = ρ} {γᵀ = γᵀ} {N = L} {N′ = L′}
      {A = ‵ `ℕ} {A′ = ‵ `ℕ} {p = idι}
      unique left-blame)
    (framed-term-backward-to-operational
      {index = index} {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      {ρ = ρ} {γᵀ = γᵀ} {N = M} {N′ = M′}
      {A = ‵ `ℕ} {A′ = ‵ `ℕ} {p = idι}
      unique right-backward)
    (framed-term-target-blame-to-operational
      {index = index} {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      {ρ = ρ} {γᵀ = γᵀ} {N = M} {N′ = M′}
      {A = ‵ `ℕ} {A′ = ‵ `ℕ} {p = idι}
      unique right-blame)

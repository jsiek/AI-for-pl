module proof.InterpreterDirectionalInstantiation where

-- File Charter:
--   * Derives directional observations for paired and left-only source
--     instantiation from operand and post-allocation tail simulations.
--   * Reuses the checked indexed instantiation composition with the
--     observation-irrelevant endpoint fixed at zero.
--   * Contains no interpreter recursion, reduction, or catch-up theorem.

open import Agda.Builtin.Equality using (_≡_; refl)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import Data.Nat using (suc; zero)

open import Interpreter
open import Simulation.Directional.InterpreterDirectionalSimulationMotive
open import Simulation.Indexed.InterpreterIndexedInstantiation
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Narrowing.InterpreterOperationalValueNarrowing
open import Typing.InterpreterSemanticTypingCore using (⟦_⟧[_])
open import Simulation.Core.InterpreterSimulationContext
open import Simulation.Core.InterpreterSimulationResult using (immediateReturn)
open import Narrowing.InterpreterTermNarrowing
import NuTerms as N
open import proof.InterpreterDirectionalSimulation using
  (backward-at-left-zero; forward-at-right-zero)
open import proof.InterpreterInstantiationTail using
  (instantiation-tail)
open import Types

open Narrowing.InterpreterTermNarrowing.RelatedWorlds

directional-paired-instantiation-forward :
  ∀ {index W W′ Φ Δᴸ Δᴿ ρ γᵀ
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
    DirectionalInterpreterTermSimulation
      forward-direction index Φ Δᴸ Δᴿ ρ γᵀ
      L L′ (`∀ C) (`∀ C′) q) →
  (∀ {C C′}
      {q : Φ ∣ Δᴸ ⊢ `∀ C ⊑ `∀ C′ ⊣ Δᴿ}
      {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    OperationalValueNarrowing
      ⟦ `∀ C ⟧[ θ ] ⟦ `∀ C′ ⟧[ θ′ ] S V V′ →
    ForwardReturnSimulation
      (OperationalValueResult
        ⟦ B ⟧[ θ ] ⟦ B′ ⟧[ θ′ ])
      S
      (instantiation-tail U θ A c V)
      (instantiation-tail U′ θ′ A′ c′ V′)
      index) →
  ForwardReturnSimulation
    (OperationalValueResult
      ⟦ B ⟧[ θ ] ⟦ B′ ⟧[ θ′ ])
    R
    (interpret W γ θ (N.ν A L c))
    (interpret W′ γ′ θ′ (N.ν A′ L′ c′))
    (suc index)
directional-paired-instantiation-forward
    {index} environment origins terms root operand tail =
  forward-return
    (indexed-paired-instantiation-suc-simulation
      {left-index = index} {right-index = zero}
      environment origins terms root
      (λ runtime₀ environment₀ origins₀ terms₀ →
        forward-at-right-zero refl
          (operand runtime₀ environment₀ origins₀ terms₀))
      (λ {C} {C′} {q} extension value →
        forward-at-right-zero refl
          (tail {C = C} {C′ = C′} {q = q} extension value)))

paired-instantiation-backward-bundle :
  ∀ {index W W′ Φ Δᴸ Δᴿ ρ γᵀ
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
    DirectionalInterpreterTermSimulation
      backward-direction index Φ Δᴸ Δᴿ ρ γᵀ
      L L′ (`∀ C) (`∀ C′) q) →
  (∀ {C C′}
      {q : Φ ∣ Δᴸ ⊢ `∀ C ⊑ `∀ C′ ⊣ Δᴿ} →
    DirectionalInterpreterTermSimulation
      target-blame-direction index Φ Δᴸ Δᴿ ρ γᵀ
      L L′ (`∀ C) (`∀ C′) q) →
  (∀ {C C′}
      {q : Φ ∣ Δᴸ ⊢ `∀ C ⊑ `∀ C′ ⊣ Δᴿ}
      {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    OperationalValueNarrowing
      ⟦ `∀ C ⟧[ θ ] ⟦ `∀ C′ ⟧[ θ′ ] S V V′ →
    BackwardReturnSimulation
      (OperationalValueResult
        ⟦ B ⟧[ θ ] ⟦ B′ ⟧[ θ′ ])
      S
      (instantiation-tail U θ A c V)
      (instantiation-tail U′ θ′ A′ c′ V′)
      index) →
  (∀ {C C′}
      {q : Φ ∣ Δᴸ ⊢ `∀ C ⊑ `∀ C′ ⊣ Δᴿ}
      {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    OperationalValueNarrowing
      ⟦ `∀ C ⟧[ θ ] ⟦ `∀ C′ ⟧[ θ′ ] S V V′ →
    TargetBlameSimulation S
      (instantiation-tail U θ A c V)
      (instantiation-tail U′ θ′ A′ c′ V′)
      index) →
  IndexedTerminalSimulation
    (OperationalValueResult
      ⟦ B ⟧[ θ ] ⟦ B′ ⟧[ θ′ ])
    R
    (interpret W γ θ (N.ν A L c))
    (interpret W′ γ′ θ′ (N.ν A′ L′ c′))
    (suc zero) (suc index)
paired-instantiation-backward-bundle
    {index} environment origins terms root
    operand-backward operand-blame tail-backward tail-blame =
  indexed-paired-instantiation-suc-simulation
    {left-index = zero} {right-index = index}
    environment origins terms root
    (λ runtime₀ environment₀ origins₀ terms₀ →
      backward-at-left-zero refl
        (operand-backward runtime₀ environment₀ origins₀ terms₀)
        (operand-blame runtime₀ environment₀ origins₀ terms₀))
    (λ {C} {C′} {q} extension value →
      backward-at-left-zero refl
        (tail-backward
          {C = C} {C′ = C′} {q = q} extension value)
        (tail-blame
          {C = C} {C′ = C′} {q = q} extension value))

directional-paired-instantiation-backward :
  ∀ {index W W′ Φ Δᴸ Δᴿ ρ γᵀ
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
    DirectionalInterpreterTermSimulation
      backward-direction index Φ Δᴸ Δᴿ ρ γᵀ
      L L′ (`∀ C) (`∀ C′) q) →
  (∀ {C C′}
      {q : Φ ∣ Δᴸ ⊢ `∀ C ⊑ `∀ C′ ⊣ Δᴿ} →
    DirectionalInterpreterTermSimulation
      target-blame-direction index Φ Δᴸ Δᴿ ρ γᵀ
      L L′ (`∀ C) (`∀ C′) q) →
  (∀ {C C′}
      {q : Φ ∣ Δᴸ ⊢ `∀ C ⊑ `∀ C′ ⊣ Δᴿ}
      {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    OperationalValueNarrowing
      ⟦ `∀ C ⟧[ θ ] ⟦ `∀ C′ ⟧[ θ′ ] S V V′ →
    BackwardReturnSimulation
      (OperationalValueResult
        ⟦ B ⟧[ θ ] ⟦ B′ ⟧[ θ′ ])
      S
      (instantiation-tail U θ A c V)
      (instantiation-tail U′ θ′ A′ c′ V′)
      index) →
  (∀ {C C′}
      {q : Φ ∣ Δᴸ ⊢ `∀ C ⊑ `∀ C′ ⊣ Δᴿ}
      {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    OperationalValueNarrowing
      ⟦ `∀ C ⟧[ θ ] ⟦ `∀ C′ ⟧[ θ′ ] S V V′ →
    TargetBlameSimulation S
      (instantiation-tail U θ A c V)
      (instantiation-tail U′ θ′ A′ c′ V′)
      index) →
  BackwardReturnSimulation
    (OperationalValueResult
      ⟦ B ⟧[ θ ] ⟦ B′ ⟧[ θ′ ])
    R
    (interpret W γ θ (N.ν A L c))
    (interpret W′ γ′ θ′ (N.ν A′ L′ c′))
    (suc index)
directional-paired-instantiation-backward
    {index} environment origins terms root
    operand-backward operand-blame tail-backward tail-blame =
  backward-return
    (paired-instantiation-backward-bundle
      {index = index}
      environment origins terms root
      operand-backward operand-blame
      (λ {C} {C′} {q} extension value →
        tail-backward {C = C} {C′ = C′} {q = q} extension value)
      (λ {C} {C′} {q} extension value →
        tail-blame {C = C} {C′ = C′} {q = q} extension value))

directional-paired-instantiation-target-blame :
  ∀ {index W W′ Φ Δᴸ Δᴿ ρ γᵀ
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
    DirectionalInterpreterTermSimulation
      backward-direction index Φ Δᴸ Δᴿ ρ γᵀ
      L L′ (`∀ C) (`∀ C′) q) →
  (∀ {C C′}
      {q : Φ ∣ Δᴸ ⊢ `∀ C ⊑ `∀ C′ ⊣ Δᴿ} →
    DirectionalInterpreterTermSimulation
      target-blame-direction index Φ Δᴸ Δᴿ ρ γᵀ
      L L′ (`∀ C) (`∀ C′) q) →
  (∀ {C C′}
      {q : Φ ∣ Δᴸ ⊢ `∀ C ⊑ `∀ C′ ⊣ Δᴿ}
      {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    OperationalValueNarrowing
      ⟦ `∀ C ⟧[ θ ] ⟦ `∀ C′ ⟧[ θ′ ] S V V′ →
    BackwardReturnSimulation
      (OperationalValueResult
        ⟦ B ⟧[ θ ] ⟦ B′ ⟧[ θ′ ])
      S
      (instantiation-tail U θ A c V)
      (instantiation-tail U′ θ′ A′ c′ V′)
      index) →
  (∀ {C C′}
      {q : Φ ∣ Δᴸ ⊢ `∀ C ⊑ `∀ C′ ⊣ Δᴿ}
      {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    OperationalValueNarrowing
      ⟦ `∀ C ⟧[ θ ] ⟦ `∀ C′ ⟧[ θ′ ] S V V′ →
    TargetBlameSimulation S
      (instantiation-tail U θ A c V)
      (instantiation-tail U′ θ′ A′ c′ V′)
      index) →
  TargetBlameSimulation R
    (interpret W γ θ (N.ν A L c))
    (interpret W′ γ′ θ′ (N.ν A′ L′ c′))
    (suc index)
directional-paired-instantiation-target-blame
    {index} environment origins terms root
    operand-backward operand-blame tail-backward tail-blame =
  target-blame-reflects
    (paired-instantiation-backward-bundle
      {index = index}
      environment origins terms root
      operand-backward operand-blame
      (λ {C} {C′} {q} extension value →
        tail-backward {C = C} {C′ = C′} {q = q} extension value)
      (λ {C} {C′} {q} extension value →
        tail-blame {C = C} {C′ = C′} {q = q} extension value))

directional-left-instantiation-forward :
  ∀ {index W W′ Φ Δᴸ Δᴿ ρ γᵀ
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
    DirectionalInterpreterTermSimulation
      forward-direction index Φ Δᴸ Δᴿ ρ γᵀ
      L N′ (`∀ C) B′ q) →
  (∀ {C}
      {q : Φ ∣ Δᴸ ⊢ `∀ C ⊑ B′ ⊣ Δᴿ}
      {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    OperationalValueNarrowing
      ⟦ `∀ C ⟧[ θ ] ⟦ B′ ⟧[ θ′ ] S V V′ →
    ForwardReturnSimulation
      (OperationalValueResult
        ⟦ B ⟧[ θ ] ⟦ B′ ⟧[ θ′ ])
      S
      (instantiation-tail U θ A c V)
      (immediateReturn U′ V′)
      index) →
  ForwardReturnSimulation
    (OperationalValueResult
      ⟦ B ⟧[ θ ] ⟦ B′ ⟧[ θ′ ])
    R
    (interpret W γ θ (N.ν A L c))
    (interpret W′ γ′ θ′ N′)
    (suc index)
directional-left-instantiation-forward
    {index} environment origins terms root operand tail =
  forward-return
    (indexed-left-instantiation-suc-simulation
      {left-index = index} {right-index = zero}
      environment origins terms root
      (λ runtime₀ environment₀ origins₀ terms₀ →
        forward-at-right-zero refl
          (operand runtime₀ environment₀ origins₀ terms₀))
      (λ {C} {q} extension value →
        forward-at-right-zero refl
          (tail {C = C} {q = q} extension value)))

left-instantiation-backward-bundle :
  ∀ {index W W′ Φ Δᴸ Δᴿ ρ γᵀ
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
    DirectionalInterpreterTermSimulation
      backward-direction index Φ Δᴸ Δᴿ ρ γᵀ
      L N′ (`∀ C) B′ q) →
  (∀ {C}
      {q : Φ ∣ Δᴸ ⊢ `∀ C ⊑ B′ ⊣ Δᴿ} →
    DirectionalInterpreterTermSimulation
      target-blame-direction index Φ Δᴸ Δᴿ ρ γᵀ
      L N′ (`∀ C) B′ q) →
  (∀ {C}
      {q : Φ ∣ Δᴸ ⊢ `∀ C ⊑ B′ ⊣ Δᴿ}
      {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    OperationalValueNarrowing
      ⟦ `∀ C ⟧[ θ ] ⟦ B′ ⟧[ θ′ ] S V V′ →
    BackwardReturnSimulation
      (OperationalValueResult
        ⟦ B ⟧[ θ ] ⟦ B′ ⟧[ θ′ ])
      S
      (instantiation-tail U θ A c V)
      (immediateReturn U′ V′)
      index) →
  (∀ {C}
      {q : Φ ∣ Δᴸ ⊢ `∀ C ⊑ B′ ⊣ Δᴿ}
      {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    OperationalValueNarrowing
      ⟦ `∀ C ⟧[ θ ] ⟦ B′ ⟧[ θ′ ] S V V′ →
    TargetBlameSimulation S
      (instantiation-tail U θ A c V)
      (immediateReturn U′ V′)
      index) →
  IndexedTerminalSimulation
    (OperationalValueResult
      ⟦ B ⟧[ θ ] ⟦ B′ ⟧[ θ′ ])
    R
    (interpret W γ θ (N.ν A L c))
    (interpret W′ γ′ θ′ N′)
    (suc zero) index
left-instantiation-backward-bundle
    {index} environment origins terms root
    operand-backward operand-blame tail-backward tail-blame =
  indexed-left-instantiation-suc-simulation
    {left-index = zero} {right-index = index}
    environment origins terms root
    (λ runtime₀ environment₀ origins₀ terms₀ →
      backward-at-left-zero refl
        (operand-backward runtime₀ environment₀ origins₀ terms₀)
        (operand-blame runtime₀ environment₀ origins₀ terms₀))
    (λ {C} {q} extension value →
      backward-at-left-zero refl
        (tail-backward {C = C} {q = q} extension value)
        (tail-blame {C = C} {q = q} extension value))

directional-left-instantiation-backward :
  ∀ {index W W′ Φ Δᴸ Δᴿ ρ γᵀ
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
    DirectionalInterpreterTermSimulation
      backward-direction index Φ Δᴸ Δᴿ ρ γᵀ
      L N′ (`∀ C) B′ q) →
  (∀ {C}
      {q : Φ ∣ Δᴸ ⊢ `∀ C ⊑ B′ ⊣ Δᴿ} →
    DirectionalInterpreterTermSimulation
      target-blame-direction index Φ Δᴸ Δᴿ ρ γᵀ
      L N′ (`∀ C) B′ q) →
  (∀ {C}
      {q : Φ ∣ Δᴸ ⊢ `∀ C ⊑ B′ ⊣ Δᴿ}
      {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    OperationalValueNarrowing
      ⟦ `∀ C ⟧[ θ ] ⟦ B′ ⟧[ θ′ ] S V V′ →
    BackwardReturnSimulation
      (OperationalValueResult
        ⟦ B ⟧[ θ ] ⟦ B′ ⟧[ θ′ ])
      S
      (instantiation-tail U θ A c V)
      (immediateReturn U′ V′)
      index) →
  (∀ {C}
      {q : Φ ∣ Δᴸ ⊢ `∀ C ⊑ B′ ⊣ Δᴿ}
      {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    OperationalValueNarrowing
      ⟦ `∀ C ⟧[ θ ] ⟦ B′ ⟧[ θ′ ] S V V′ →
    TargetBlameSimulation S
      (instantiation-tail U θ A c V)
      (immediateReturn U′ V′)
      index) →
  BackwardReturnSimulation
    (OperationalValueResult
      ⟦ B ⟧[ θ ] ⟦ B′ ⟧[ θ′ ])
    R
    (interpret W γ θ (N.ν A L c))
    (interpret W′ γ′ θ′ N′)
    index
directional-left-instantiation-backward
    {index} environment origins terms root
    operand-backward operand-blame tail-backward tail-blame =
  backward-return
    (left-instantiation-backward-bundle
      {index = index}
      environment origins terms root
      operand-backward operand-blame
      (λ {C} {q} extension value →
        tail-backward {C = C} {q = q} extension value)
      (λ {C} {q} extension value →
        tail-blame {C = C} {q = q} extension value))

directional-left-instantiation-target-blame :
  ∀ {index W W′ Φ Δᴸ Δᴿ ρ γᵀ
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
    DirectionalInterpreterTermSimulation
      backward-direction index Φ Δᴸ Δᴿ ρ γᵀ
      L N′ (`∀ C) B′ q) →
  (∀ {C}
      {q : Φ ∣ Δᴸ ⊢ `∀ C ⊑ B′ ⊣ Δᴿ} →
    DirectionalInterpreterTermSimulation
      target-blame-direction index Φ Δᴸ Δᴿ ρ γᵀ
      L N′ (`∀ C) B′ q) →
  (∀ {C}
      {q : Φ ∣ Δᴸ ⊢ `∀ C ⊑ B′ ⊣ Δᴿ}
      {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    OperationalValueNarrowing
      ⟦ `∀ C ⟧[ θ ] ⟦ B′ ⟧[ θ′ ] S V V′ →
    BackwardReturnSimulation
      (OperationalValueResult
        ⟦ B ⟧[ θ ] ⟦ B′ ⟧[ θ′ ])
      S
      (instantiation-tail U θ A c V)
      (immediateReturn U′ V′)
      index) →
  (∀ {C}
      {q : Φ ∣ Δᴸ ⊢ `∀ C ⊑ B′ ⊣ Δᴿ}
      {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    OperationalValueNarrowing
      ⟦ `∀ C ⟧[ θ ] ⟦ B′ ⟧[ θ′ ] S V V′ →
    TargetBlameSimulation S
      (instantiation-tail U θ A c V)
      (immediateReturn U′ V′)
      index) →
  TargetBlameSimulation R
    (interpret W γ θ (N.ν A L c))
    (interpret W′ γ′ θ′ N′)
    index
directional-left-instantiation-target-blame
    {index} environment origins terms root
    operand-backward operand-blame tail-backward tail-blame =
  target-blame-reflects
    (left-instantiation-backward-bundle
      {index = index}
      environment origins terms root
      operand-backward operand-blame
      (λ {C} {q} extension value →
        tail-backward {C = C} {q = q} extension value)
      (λ {C} {q} extension value →
        tail-blame {C = C} {q = q} extension value))

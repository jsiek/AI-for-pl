module proof.InterpreterDirectionalRightCast where

-- File Charter:
--   * Composes a source term with a target-only coercion application.
--   * Makes the asymmetric fuel discipline explicit: forward uses the
--     current term/coercion observations, while backward and blame use the
--     predecessor observations under the target guard.
--   * Contains no recursive definition, reduction, or catch-up theorem.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat using (suc; zero)
open import Data.Product using (_×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (sym)

open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import Interpreter
open import Narrowing.InterpreterCoercionNarrowing
open import Simulation.Coercion.InterpreterCoercionSimulationMotive using
  (executeCoercionAction)
open import Simulation.Directional.InterpreterDirectionalSimulationMotive
open import Narrowing.InterpreterFramedValueNarrowing
open import Narrowing.InterpreterReachableCoercionNarrowing using
  (right-component-reachable)
open import Core.InterpreterFuel using
  (coerceValue-terminal-stable; interpret-terminal-stable)
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Simulation.Core.InterpreterSimulationContext
open import Simulation.Core.InterpreterSimulationResult using
  (chain; guard; immediateReturn)
open import Narrowing.InterpreterTermNarrowing
import NuTermImprecision as NTI
import NuTerms as N
open import proof.InterpreterDirectionalGuard using
  ( right-guard-backward
  ; right-guard-forward
  ; right-guard-target-blame
  )
open import proof.InterpreterDirectionalSequence using
  ( directional-right-chain-backward
  ; directional-right-chain-forward
  ; directional-right-chain-target-blame
  )
open import proof.InterpreterDirectionalTransport using
  (backward-pointwise; forward-pointwise; target-blame-pointwise)
open import
  proof.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import Types

open Narrowing.InterpreterTermNarrowing.RelatedWorlds

right-cast-computation :
  ∀ {W γ θ M c} n →
  interpret W γ θ (M N.⟨ c ⟩) n ≡
  guard W
    (chain (interpret W γ θ M)
      (λ U V → coerceValue U θ c V))
    n
right-cast-computation {W} {γ} {θ} {M} {c} zero =
  refl
right-cast-computation {W} {γ} {θ} {M} {c} (suc n)
    with interpret W γ θ M n
right-cast-computation {W} {γ} {θ} {M} {c} (suc n)
    | timed U =
  refl
right-cast-computation {W} {γ} {θ} {M} {c} (suc n)
    | blamed U =
  refl
right-cast-computation {W} {γ} {θ} {M} {c} (suc n)
    | failed U e =
  refl
right-cast-computation {W} {γ} {θ} {M} {c} (suc n)
    | returned U V =
  refl

directional-right-cast-forward :
  ∀ {index W W′ Φ Δᴸ Δᴿ ρ γᵀ
      θ θ′ γ γ′ M M′ c′ A A′ B′ p q}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  AssumptionMembershipUnique Φ →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  FramedEnvironmentNarrowing runtime γᵀ γ γ′ →
  (body :
    OpenInterpreterTermNarrowing
      R Φ Δᴸ Δᴿ ρ γᵀ M M′ A A′ p) →
  (action :
    ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
      skip-coercion (apply-coercion c′)
      {A} {A′} {A} {B′} p q) →
  FramedDirectionalInterpreterTermSimulation
    forward-direction (suc index)
    Φ Δᴸ Δᴿ ρ γᵀ M M′ A A′ p →
  FramedDirectionalCoercionSimulation
    forward-direction (suc index) →
  ForwardReturnSimulation
    (FramedValueResult ρ θ θ′ q) R
    (interpret W γ θ M)
    (interpret W′ γ′ θ′ (M′ N.⟨ c′ ⟩))
    (suc index)
directional-right-cast-forward
    {index} {W} {W′} {ρ = ρ} {θ = θ} {θ′} {γ} {γ′} {M = M}
    {M′} {c′} {p = p} {q = q} {R = R} {runtime = runtime}
    unique environment origins body action term coercion =
  forward-pointwise
    {left-index = suc index}
    {value-result = FramedValueResult ρ θ θ′ q}
    {R = R}
    {left = interpret W γ θ M}
    {left′ = interpret W γ θ M}
    {right =
      guard W′
        (chain (interpret W′ γ′ θ′ M′)
          (λ U′ V′ → coerceValue U′ θ′ c′ V′))}
    {right′ = interpret W′ γ′ θ′ (M′ N.⟨ c′ ⟩)}
    (λ n → refl)
    (λ n → sym (right-cast-computation n))
    (right-guard-forward
      {W = W} {W′ = W′} {U′ = W′}
      {left-index = suc index}
      {value-result = FramedValueResult ρ θ θ′ q}
      {R = R}
      {left = interpret W γ θ M}
      {right =
        chain (interpret W′ γ′ θ′ M′)
          (λ U′ V′ → coerceValue U′ θ′ c′ V′)}
      refl chained)
  where
  chained =
    directional-right-chain-forward
      {W = W} {W′ = W′} {left-index = suc index}
      {head-result = FramedValueResult ρ θ θ′ p}
      {continuation-result = FramedValueResult ρ θ θ′ q}
      {R = R}
      {left-head = interpret W γ θ M}
      {right-head = interpret W′ γ′ θ′ M′}
      {right-continuation =
        λ U′ V′ → coerceValue U′ θ′ c′ V′}
      (term unique runtime environment origins body)
      (λ
        { R≤S (framed-result runtimeS value) →
            coercion unique runtimeS
              (right-component-reachable action) value
        })
      refl refl
      (λ U′ V′ → refl)
      (λ { {n} {o} terminal eq k →
        interpret-terminal-stable
          {W = W′} {γ = γ′} {θ = θ′} {M = M′}
          {n = n} {o = o} terminal eq k
        })
      (λ U′ V′ {n} {o} terminal eq k →
        coerceValue-terminal-stable
          {W = U′} {θ = θ′} {c = c′} {V = V′}
          {n = n} {o = o} terminal eq k)

directional-right-cast-backward :
  ∀ {index W W′ Φ Δᴸ Δᴿ ρ γᵀ
      θ θ′ γ γ′ M M′ c′ A A′ B′ p q}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  AssumptionMembershipUnique Φ →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  FramedEnvironmentNarrowing runtime γᵀ γ γ′ →
  (body :
    OpenInterpreterTermNarrowing
      R Φ Δᴸ Δᴿ ρ γᵀ M M′ A A′ p) →
  (action :
    ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
      skip-coercion (apply-coercion c′)
      {A} {A′} {A} {B′} p q) →
  (FramedDirectionalInterpreterTermSimulation
      backward-direction index
      Φ Δᴸ Δᴿ ρ γᵀ M M′ A A′ p
   × FramedDirectionalInterpreterTermSimulation
      target-blame-direction index
      Φ Δᴸ Δᴿ ρ γᵀ M M′ A A′ p) →
  (FramedDirectionalCoercionSimulation backward-direction index
   × FramedDirectionalCoercionSimulation
      target-blame-direction index) →
  BackwardReturnSimulation
    (FramedValueResult ρ θ θ′ q) R
    (interpret W γ θ M)
    (interpret W′ γ′ θ′ (M′ N.⟨ c′ ⟩))
    (suc index)
directional-right-cast-backward
    {index} {W} {W′} {ρ = ρ} {θ = θ} {θ′} {γ} {γ′} {M = M}
    {M′} {c′} {p = p} {q = q} {R = R} {runtime = runtime}
    unique environment origins body action term coercion =
  backward-pointwise
    {right-index = suc index}
    {value-result = FramedValueResult ρ θ θ′ q}
    {R = R}
    {left = interpret W γ θ M}
    {left′ = interpret W γ θ M}
    {right =
      guard W′
        (chain (interpret W′ γ′ θ′ M′)
          (λ U′ V′ → coerceValue U′ θ′ c′ V′))}
    {right′ = interpret W′ γ′ θ′ (M′ N.⟨ c′ ⟩)}
    (λ n → refl)
    (λ n → sym (right-cast-computation n))
    (right-guard-backward
      {W = W} {W′ = W′} {U′ = W′}
      {right-index = index}
      {value-result = FramedValueResult ρ θ θ′ q}
      {R = R}
      {left = interpret W γ θ M}
      {right =
        chain (interpret W′ γ′ θ′ M′)
          (λ U′ V′ → coerceValue U′ θ′ c′ V′)}
      refl chained-backward chained-blame)
  where
  chained-backward =
    directional-right-chain-backward
      {W = W} {W′ = W′} {right-index = index}
      {head-result = FramedValueResult ρ θ θ′ p}
      {continuation-result = FramedValueResult ρ θ θ′ q}
      {R = R}
      {left-head = interpret W γ θ M}
      {right-head = interpret W′ γ′ θ′ M′}
      {right-continuation =
        λ U′ V′ → coerceValue U′ θ′ c′ V′}
      (proj₁ term unique runtime environment origins body)
      (proj₂ term unique runtime environment origins body)
      (λ
        { R≤S (framed-result runtimeS value) →
            proj₁ coercion unique runtimeS
              (right-component-reachable action) value
        })
      (λ
        { R≤S (framed-result runtimeS value) →
            proj₂ coercion unique runtimeS
              (right-component-reachable action) value
        })
      refl
      (λ { {n} {o} terminal eq k →
        interpret-terminal-stable
          {W = W′} {γ = γ′} {θ = θ′} {M = M′}
          {n = n} {o = o} terminal eq k
        })
      (λ U′ V′ {n} {o} terminal eq k →
        coerceValue-terminal-stable
          {W = U′} {θ = θ′} {c = c′} {V = V′}
          {n = n} {o = o} terminal eq k)

  chained-blame =
    directional-right-chain-target-blame
      {W = W} {W′ = W′} {right-index = index}
      {head-result = FramedValueResult ρ θ θ′ p}
      {continuation-result = FramedValueResult ρ θ θ′ q}
      {R = R}
      {left-head = interpret W γ θ M}
      {right-head = interpret W′ γ′ θ′ M′}
      {right-continuation =
        λ U′ V′ → coerceValue U′ θ′ c′ V′}
      (proj₁ term unique runtime environment origins body)
      (proj₂ term unique runtime environment origins body)
      (λ
        { R≤S (framed-result runtimeS value) →
            proj₁ coercion unique runtimeS
              (right-component-reachable action) value
        })
      (λ
        { R≤S (framed-result runtimeS value) →
            proj₂ coercion unique runtimeS
              (right-component-reachable action) value
        })
      refl
      (λ { {n} {o} terminal eq k →
        interpret-terminal-stable
          {W = W′} {γ = γ′} {θ = θ′} {M = M′}
          {n = n} {o = o} terminal eq k
        })
      (λ U′ V′ {n} {o} terminal eq k →
        coerceValue-terminal-stable
          {W = U′} {θ = θ′} {c = c′} {V = V′}
          {n = n} {o = o} terminal eq k)

directional-right-cast-target-blame :
  ∀ {index W W′ Φ Δᴸ Δᴿ ρ γᵀ
      θ θ′ γ γ′ M M′ c′ A A′ B′ p q}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  AssumptionMembershipUnique Φ →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  FramedEnvironmentNarrowing runtime γᵀ γ γ′ →
  (body :
    OpenInterpreterTermNarrowing
      R Φ Δᴸ Δᴿ ρ γᵀ M M′ A A′ p) →
  (action :
    ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
      skip-coercion (apply-coercion c′)
      {A} {A′} {A} {B′} p q) →
  (FramedDirectionalInterpreterTermSimulation
      backward-direction index
      Φ Δᴸ Δᴿ ρ γᵀ M M′ A A′ p
   × FramedDirectionalInterpreterTermSimulation
      target-blame-direction index
      Φ Δᴸ Δᴿ ρ γᵀ M M′ A A′ p) →
  (FramedDirectionalCoercionSimulation backward-direction index
   × FramedDirectionalCoercionSimulation
      target-blame-direction index) →
  TargetBlameSimulation R
    (interpret W γ θ M)
    (interpret W′ γ′ θ′ (M′ N.⟨ c′ ⟩))
    (suc index)
directional-right-cast-target-blame
    {index} {W} {W′} {ρ = ρ} {θ = θ} {θ′} {γ} {γ′} {M = M}
    {M′} {c′} {p = p} {q = q} {R = R} {runtime = runtime}
    unique environment origins body action term coercion =
  target-blame-pointwise
    {right-index = suc index}
    {R = R}
    {left = interpret W γ θ M}
    {left′ = interpret W γ θ M}
    {right =
      guard W′
        (chain (interpret W′ γ′ θ′ M′)
          (λ U′ V′ → coerceValue U′ θ′ c′ V′))}
    {right′ = interpret W′ γ′ θ′ (M′ N.⟨ c′ ⟩)}
    (λ n → refl)
    (λ n → sym (right-cast-computation n))
    (right-guard-target-blame
      {W = W} {W′ = W′} {U′ = W′}
      {right-index = index} {R = R}
      {left = interpret W γ θ M}
      {right =
        chain (interpret W′ γ′ θ′ M′)
          (λ U′ V′ → coerceValue U′ θ′ c′ V′)}
      refl chained-backward chained-blame)
  where
  chained-backward =
    directional-right-chain-backward
      {W = W} {W′ = W′} {right-index = index}
      {head-result = FramedValueResult ρ θ θ′ p}
      {continuation-result = FramedValueResult ρ θ θ′ q}
      {R = R}
      {left-head = interpret W γ θ M}
      {right-head = interpret W′ γ′ θ′ M′}
      {right-continuation =
        λ U′ V′ → coerceValue U′ θ′ c′ V′}
      (proj₁ term unique runtime environment origins body)
      (proj₂ term unique runtime environment origins body)
      (λ
        { R≤S (framed-result runtimeS value) →
            proj₁ coercion unique runtimeS
              (right-component-reachable action) value
        })
      (λ
        { R≤S (framed-result runtimeS value) →
            proj₂ coercion unique runtimeS
              (right-component-reachable action) value
        })
      refl
      (λ { {n} {o} terminal eq k →
        interpret-terminal-stable
          {W = W′} {γ = γ′} {θ = θ′} {M = M′}
          {n = n} {o = o} terminal eq k
        })
      (λ U′ V′ {n} {o} terminal eq k →
        coerceValue-terminal-stable
          {W = U′} {θ = θ′} {c = c′} {V = V′}
          {n = n} {o = o} terminal eq k)

  chained-blame =
    directional-right-chain-target-blame
      {W = W} {W′ = W′} {right-index = index}
      {head-result = FramedValueResult ρ θ θ′ p}
      {continuation-result = FramedValueResult ρ θ θ′ q}
      {R = R}
      {left-head = interpret W γ θ M}
      {right-head = interpret W′ γ′ θ′ M′}
      {right-continuation =
        λ U′ V′ → coerceValue U′ θ′ c′ V′}
      (proj₁ term unique runtime environment origins body)
      (proj₂ term unique runtime environment origins body)
      (λ
        { R≤S (framed-result runtimeS value) →
            proj₁ coercion unique runtimeS
              (right-component-reachable action) value
        })
      (λ
        { R≤S (framed-result runtimeS value) →
            proj₂ coercion unique runtimeS
              (right-component-reachable action) value
        })
      refl
      (λ { {n} {o} terminal eq k →
        interpret-terminal-stable
          {W = W′} {γ = γ′} {θ = θ′} {M = M′}
          {n = n} {o = o} terminal eq k
        })
      (λ U′ V′ {n} {o} terminal eq k →
        coerceValue-terminal-stable
          {W = U′} {θ = θ′} {c = c′} {V = V′}
          {n = n} {o = o} terminal eq k)

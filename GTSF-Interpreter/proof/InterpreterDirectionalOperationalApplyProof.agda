module proof.InterpreterDirectionalOperationalApplyProof where

-- File Charter:
--   * Implements positive-fuel operational application in all three
--     constructive terminal directions.
--   * Dispatches closures and reachable function proxies directly.
--   * Delegates only name-instantiated and quotient-origin functions to
--     explicit structural callbacks.
--   * Contains no small-step reduction or catch-up theorem.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (_∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (sym)

open import Interpreter
open import Simulation.Coercion.InterpreterCoercionComponents
open import Simulation.Directional.InterpreterDirectionalSimulationMotive
open import Narrowing.InterpreterFramedValueNarrowingProperties using
  (operational-environment-frame)
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Narrowing.InterpreterOperationalValueNarrowing
open import Narrowing.InterpreterOperationalValueNarrowingProperties
open import Narrowing.InterpreterReachableCoercionNarrowing using
  ( left-component-reachable
  ; paired-conversion-function-components-reachable
  ; right-component-reachable
  )
open import Typing.InterpreterSemanticTypingCore
open import Simulation.Core.InterpreterSimulationContext
open import Simulation.Core.InterpreterSimulationContextProperties using
  (runtime-narrowing-weaken)
open import Simulation.Core.InterpreterSimulationResult using (guard)
open import Narrowing.InterpreterTermNarrowing
open import Narrowing.InterpreterTypedValueNarrowing
import NuTermImprecision as NTI
open import proof.InterpreterDirectionalFraming using
  (framed-backward-to-operational; framed-forward-to-operational)
open import proof.InterpreterDirectionalFunctionProxy using
  ( left-function-proxy-backward-bundle
  ; paired-function-proxy-backward-bundle
  ; right-function-proxy-backward-bundle
  ; directional-left-function-proxy-forward
  ; directional-paired-function-proxy-forward
  ; directional-right-function-proxy-forward
  )
open import proof.InterpreterDirectionalGuard using
  ( paired-guard-backward
  ; paired-guard-forward
  ; paired-guard-target-blame
  )
open import proof.InterpreterDirectionalTransport using
  (backward-pointwise; forward-pointwise; target-blame-pointwise)
open import proof.InterpreterOperationalEnvironmentLift using
  (operational-value-type-transport)
open import Types

open Narrowing.InterpreterTermNarrowing.InterpreterValues
open Narrowing.InterpreterTermNarrowing.RelatedWorlds


closure-application-computation :
  ∀ {W N γ θ U} n →
  applyValue W (closure N γ θ) U n ≡
  guard W (interpret W (U ∷ γ) θ N) n
closure-application-computation zero =
  refl
closure-application-computation (suc n) =
  refl


closure-application-forward :
  ∀ {index W W′ Φ Δᴸ Δᴿ ρ γᵀ θ θ′ γ γ′
      N N′ A A′ B B′ U U′ pA pB R} →
  FramedDirectionalInterpreterTermSimulation
    forward-direction index Φ Δᴸ Δᴿ ρ
    (NTI.ctx-imp A A′ pA ∷ γᵀ) N N′ B B′ pB →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  EnvironmentRealization runtime γᵀ γ γ′ →
  OperationalEnvironmentNarrowing θ θ′ R γᵀ γ γ′ →
  OpenInterpreterTermNarrowing R Φ Δᴸ Δᴿ ρ
    (NTI.ctx-imp A A′ pA ∷ γᵀ) N N′ B B′ pB →
  OperationalValueNarrowing
    ⟦ A ⟧[ θ ] ⟦ A′ ⟧[ θ′ ] R U U′ →
  ForwardReturnSimulation
    (OperationalValueResult ⟦ B ⟧[ θ ] ⟦ B′ ⟧[ θ′ ]) R
    (applyValue W (closure N γ θ) U)
    (applyValue W′ (closure N′ γ′ θ′) U′)
    (suc index)
closure-application-forward
    {index} {W} {W′} {Φ} {Δᴸ} {Δᴿ} {ρ} {γᵀ}
    {θ} {θ′} {γ} {γ′} {N} {N′} {A} {A′} {B} {B′}
    {U} {U′} {pA} {pB} {R}
    term-simulation runtime environment origins terms argument =
  forward-pointwise
    {W = W} {W′ = W′} {left-index = suc index}
    {value-result =
      OperationalValueResult ⟦ B ⟧[ θ ] ⟦ B′ ⟧[ θ′ ]}
    {R = R}
    {left = guard W (interpret W (U ∷ γ) θ N)}
    {left′ = applyValue W (closure N γ θ) U}
    {right = guard W′ (interpret W′ (U′ ∷ γ′) θ′ N′)}
    {right′ = applyValue W′ (closure N′ γ′ θ′) U′}
    (λ n → sym (closure-application-computation n))
    (λ n → sym (closure-application-computation n))
    (paired-guard-forward
      {W = W} {W′ = W′} {U = W} {U′ = W′}
      {left-index = index}
      {value-result =
        OperationalValueResult ⟦ B ⟧[ θ ] ⟦ B′ ⟧[ θ′ ]}
      {R = R}
      {left = interpret W (U ∷ γ) θ N}
      {right = interpret W′ (U′ ∷ γ′) θ′ N′}
      refl
      (framed-forward-to-operational
        {left-index = index} {ρ = ρ} {θ = θ} {θ′ = θ′}
        {A = B} {A′ = B′} {p = pB} {R = R}
        {left = interpret W (U ∷ γ) θ N}
        {right = interpret W′ (U′ ∷ γ′) θ′ N′}
        (term-simulation
          (assumption-membership-unique runtime)
          runtime
          (environment-realization
            (values-narrow (operational-typed argument) ∷⊑∷ᵉ
             environments-narrow environment)
            (environment-cons
              (left-value-typed (operational-typed argument))
              (left-environment-typed environment))
            (environment-cons
              (right-value-typed (operational-typed argument))
              (right-environment-typed environment)))
          (operational-environment-frame runtime
            (argument ∷⊑∷ᵒ origins))
          terms)))


closure-application-backward :
  ∀ {index W W′ Φ Δᴸ Δᴿ ρ γᵀ θ θ′ γ γ′
      N N′ A A′ B B′ U U′ pA pB R} →
  (FramedDirectionalInterpreterTermSimulation
     backward-direction index Φ Δᴸ Δᴿ ρ
     (NTI.ctx-imp A A′ pA ∷ γᵀ) N N′ B B′ pB
   ×
   FramedDirectionalInterpreterTermSimulation
     target-blame-direction index Φ Δᴸ Δᴿ ρ
     (NTI.ctx-imp A A′ pA ∷ γᵀ) N N′ B B′ pB) →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  EnvironmentRealization runtime γᵀ γ γ′ →
  OperationalEnvironmentNarrowing θ θ′ R γᵀ γ γ′ →
  OpenInterpreterTermNarrowing R Φ Δᴸ Δᴿ ρ
    (NTI.ctx-imp A A′ pA ∷ γᵀ) N N′ B B′ pB →
  OperationalValueNarrowing
    ⟦ A ⟧[ θ ] ⟦ A′ ⟧[ θ′ ] R U U′ →
  BackwardReturnSimulation
    (OperationalValueResult ⟦ B ⟧[ θ ] ⟦ B′ ⟧[ θ′ ]) R
    (applyValue W (closure N γ θ) U)
    (applyValue W′ (closure N′ γ′ θ′) U′)
    (suc index)
  ×
  TargetBlameSimulation R
    (applyValue W (closure N γ θ) U)
    (applyValue W′ (closure N′ γ′ θ′) U′)
    (suc index)
closure-application-backward
    {index} {W} {W′} {Φ} {Δᴸ} {Δᴿ} {ρ} {γᵀ}
    {θ} {θ′} {γ} {γ′} {N} {N′} {A} {A′} {B} {B′}
    {U} {U′} {pA} {pB} {R}
    term-simulation runtime environment origins terms argument =
  backward-pointwise
    {W = W} {W′ = W′} {right-index = suc index}
    {value-result =
      OperationalValueResult ⟦ B ⟧[ θ ] ⟦ B′ ⟧[ θ′ ]}
    {R = R}
    {left = guard W (interpret W (U ∷ γ) θ N)}
    {left′ = applyValue W (closure N γ θ) U}
    {right = guard W′ (interpret W′ (U′ ∷ γ′) θ′ N′)}
    {right′ = applyValue W′ (closure N′ γ′ θ′) U′}
    (λ n → sym (closure-application-computation n))
    (λ n → sym (closure-application-computation n))
    (paired-guard-backward
      {W = W} {W′ = W′} {U = W} {U′ = W′}
      {right-index = index}
      {value-result =
        OperationalValueResult ⟦ B ⟧[ θ ] ⟦ B′ ⟧[ θ′ ]}
      {R = R}
      {left = interpret W (U ∷ γ) θ N}
      {right = interpret W′ (U′ ∷ γ′) θ′ N′}
      refl body-backward body-blame) ,
  target-blame-pointwise
    {W = W} {W′ = W′} {right-index = suc index}
    {R = R}
    {left = guard W (interpret W (U ∷ γ) θ N)}
    {left′ = applyValue W (closure N γ θ) U}
    {right = guard W′ (interpret W′ (U′ ∷ γ′) θ′ N′)}
    {right′ = applyValue W′ (closure N′ γ′ θ′) U′}
    (λ n → sym (closure-application-computation n))
    (λ n → sym (closure-application-computation n))
    (paired-guard-target-blame
      {W = W} {W′ = W′} {U = W} {U′ = W′}
      {right-index = index} {R = R}
      {left = interpret W (U ∷ γ) θ N}
      {right = interpret W′ (U′ ∷ γ′) θ′ N′}
      refl body-backward body-blame)
  where
  environment′ =
    environment-realization
      (values-narrow (operational-typed argument) ∷⊑∷ᵉ
       environments-narrow environment)
      (environment-cons
        (left-value-typed (operational-typed argument))
        (left-environment-typed environment))
      (environment-cons
        (right-value-typed (operational-typed argument))
        (right-environment-typed environment))

  origins′ =
    operational-environment-frame runtime
      (argument ∷⊑∷ᵒ origins)

  body-backward =
    framed-backward-to-operational
      {right-index = index} {ρ = ρ} {θ = θ} {θ′ = θ′}
      {A = B} {A′ = B′} {p = pB} {R = R}
      {left = interpret W (U ∷ γ) θ N}
      {right = interpret W′ (U′ ∷ γ′) θ′ N′}
      (proj₁ term-simulation
        (assumption-membership-unique runtime)
        runtime environment′ origins′ terms)

  body-blame =
    proj₂ term-simulation
      (assumption-membership-unique runtime)
      runtime environment′ origins′ terms


directional-operational-apply-forward-positive :
  ∀ {index} →
  (∀ {Φ Δᴸ Δᴿ ρ γᵀ N N′ A B p} →
    FramedDirectionalInterpreterTermSimulation
      forward-direction index Φ Δᴸ Δᴿ ρ γᵀ N N′ A B p) →
  DirectionalCoercionSimulation forward-direction index →
  DirectionalApplyValueSimulation forward-direction index →
  DirectionalCoercionSimulation forward-direction (suc index) →
  DirectionalApplyValueSimulation forward-direction (suc index) →
  (∀ {W W′ A A′ B B′ V V′ U U′}
      {R : WorldRelation W W′} →
    (value : OperationalValueNarrowing
      (A ⇒ᵛ B) (A′ ⇒ᵛ B′) R V V′) →
    NameInstantiatedOperationalOrigin (operational-origin value) →
    OperationalValueNarrowing A A′ R U U′ →
    ForwardReturnSimulation
      (OperationalValueResult B B′) R
      (applyValue W V U) (applyValue W′ V′ U′)
      (suc index)) →
  (∀ {W W′ A A′ B B′ V V′ U U′}
      {R : WorldRelation W W′} →
    (value : OperationalValueNarrowing
      (A ⇒ᵛ B) (A′ ⇒ᵛ B′) R V V′) →
    QuotientOperationalOrigin (operational-origin value) →
    OperationalValueNarrowing A A′ R U U′ →
    ForwardReturnSimulation
      (OperationalValueResult B B′) R
      (applyValue W V U) (applyValue W′ V′ U′)
      (suc index)) →
  DirectionalApplyValueSimulation forward-direction (suc index)
directional-operational-apply-forward-positive
    {index} term-simulation coercion application
    right-coercion right-application instantiated quotient
    (operational-value typed
      (closure-origin runtime environment origins terms))
    argument =
  closure-application-forward
    {index = index}
    term-simulation runtime environment origins terms argument
directional-operational-apply-forward-positive
    {index} term-simulation coercion application
    right-coercion right-application instantiated quotient
    (operational-value typed
      (paired-function-origin runtime action domain codomain value))
    argument =
  directional-paired-function-proxy-forward {index = index}
    (coercion runtime (proj₁ components) argument)
    (λ R≤S domain-value →
      application
        (operational-value-narrowing-weaken R≤S
          (left-world-typed (operational-typed domain-value))
          (right-world-typed (operational-typed domain-value))
          value)
        domain-value)
    (λ R≤S application-value →
      coercion
        (runtime-narrowing-weaken R≤S
          (left-world-typed (operational-typed application-value))
          (right-world-typed (operational-typed application-value))
          runtime)
        (proj₂ components) application-value)
  where
  components =
    paired-conversion-function-components-reachable action
directional-operational-apply-forward-positive
    {index} term-simulation coercion application
    right-coercion right-application instantiated quotient
    (operational-value typed
      (left-function-origin runtime action domain codomain value))
    argument =
  directional-left-function-proxy-forward {index = index}
    (coercion runtime
      (left-component-reachable domain) argument)
    (λ R≤S domain-value →
      application
        (operational-value-narrowing-weaken R≤S
          (left-world-typed (operational-typed domain-value))
          (right-world-typed (operational-typed domain-value))
          value)
        domain-value)
    (λ R≤S application-value →
      coercion
        (runtime-narrowing-weaken R≤S
          (left-world-typed (operational-typed application-value))
          (right-world-typed (operational-typed application-value))
          runtime)
        (left-component-reachable codomain) application-value)
directional-operational-apply-forward-positive
    {index} term-simulation coercion application
    right-coercion right-application instantiated quotient
    (operational-value typed
      (right-function-components-origin
        {V = V₀} {V′ = V₀′}
        runtime action domain codomain value))
    argument =
  directional-right-function-proxy-forward
    {V = V₀} {V′ = V₀′} {index = suc index}
    (right-coercion runtime
      (right-component-reachable domain) argument)
    (λ R≤S domain-value →
      right-application
        (operational-value-narrowing-weaken R≤S
          (left-world-typed (operational-typed domain-value))
          (right-world-typed (operational-typed domain-value))
          value)
        domain-value)
    (λ R≤S application-value →
      right-coercion
        (runtime-narrowing-weaken R≤S
          (left-world-typed (operational-typed application-value))
          (right-world-typed (operational-typed application-value))
          runtime)
        (right-component-reachable codomain) application-value)
directional-operational-apply-forward-positive
    {index} term-simulation coercion application
    right-coercion right-application instantiated quotient
    (operational-value typed
      (right-function-origin runtime action value))
    argument
    with right-function-coercion-components action
directional-operational-apply-forward-positive
    {index} term-simulation coercion application
    right-coercion right-application instantiated quotient
    (operational-value typed
      (right-function-origin runtime action value))
    argument
    | domain , codomain =
  directional-operational-apply-forward-positive
    term-simulation coercion application
    right-coercion right-application instantiated quotient
    (operational-value typed
      (right-function-components-origin
        runtime action domain codomain value))
    argument
directional-operational-apply-forward-positive
    {index} term-simulation coercion application
    right-coercion right-application instantiated quotient
    (operational-value typed
      (right-function-boundary-origin
        {V = V₀} {V′ = V₀′}
        runtime action origin-value left-eq))
    argument
    with right-boundary-function-coercion-components left-eq action
directional-operational-apply-forward-positive
    {index} term-simulation coercion application
    right-coercion right-application instantiated quotient
    (operational-value typed
      (right-function-boundary-origin
        {V = V₀} {V′ = V₀′}
        runtime action origin-value left-eq))
    argument
    | S₁ , S₂ , A₁′ , B₁′ , pA , pB , pC , pD ,
      refl , refl , refl , domain , codomain =
  directional-right-function-proxy-forward
    {V = V₀} {V′ = V₀′} {index = suc index}
    (right-coercion runtime
      (right-component-reachable domain) argument)
    (λ R≤S domain-value →
      right-application
        (operational-value-narrowing-weaken R≤S
          (left-world-typed (operational-typed domain-value))
          (right-world-typed (operational-typed domain-value))
          (operational-value-type-transport
            (sym left-eq) refl origin-value))
        domain-value)
    (λ R≤S application-value →
      right-coercion
        (runtime-narrowing-weaken R≤S
          (left-world-typed (operational-typed application-value))
          (right-world-typed (operational-typed application-value))
          runtime)
        (right-component-reachable codomain) application-value)
directional-operational-apply-forward-positive
    {index} term-simulation coercion application
    right-coercion right-application instantiated quotient
    value@(operational-value typed
      (left-name-instantiated-origin R≤S α-ok result-eq origin-value))
    argument =
  instantiated value name-instantiated-operational-origin argument
directional-operational-apply-forward-positive
    {index} term-simulation coercion application
    right-coercion right-application instantiated quotient
    value@(operational-value typed
      (operational-quotient-origin
        runtime D⊑E alignment down up left-eq right-eq
        frame origin-value))
    argument =
  quotient value active-quotient-operational-origin argument
directional-operational-apply-forward-positive
    {index} term-simulation coercion application
    right-coercion right-application instantiated quotient
    value@(operational-value typed
      (quotient-origin runtime base terms left-eq right-eq
        frame origin-value))
    argument =
  quotient value quotient-operational-origin argument


directional-operational-apply-backward-result-positive :
  ∀ {index} →
  (∀ {Φ Δᴸ Δᴿ ρ γᵀ N N′ A B p} →
    FramedDirectionalInterpreterTermSimulation
      backward-direction index Φ Δᴸ Δᴿ ρ γᵀ N N′ A B p
    ×
    FramedDirectionalInterpreterTermSimulation
      target-blame-direction index Φ Δᴸ Δᴿ ρ γᵀ N N′ A B p) →
  (DirectionalCoercionSimulation backward-direction index
   × DirectionalCoercionSimulation target-blame-direction index) →
  (DirectionalApplyValueSimulation backward-direction index
   × DirectionalApplyValueSimulation target-blame-direction index) →
  (DirectionalCoercionSimulation backward-direction (suc index)
   ×
   DirectionalCoercionSimulation
     target-blame-direction (suc index)) →
  (DirectionalApplyValueSimulation backward-direction (suc index)
   ×
   DirectionalApplyValueSimulation
     target-blame-direction (suc index)) →
  (∀ {W W′ A A′ B B′ V V′ U U′}
      {R : WorldRelation W W′} →
    (value : OperationalValueNarrowing
      (A ⇒ᵛ B) (A′ ⇒ᵛ B′) R V V′) →
    NameInstantiatedOperationalOrigin (operational-origin value) →
    OperationalValueNarrowing A A′ R U U′ →
    BackwardReturnSimulation
      (OperationalValueResult B B′) R
      (applyValue W V U) (applyValue W′ V′ U′)
      (suc index)
    ×
    TargetBlameSimulation R
      (applyValue W V U) (applyValue W′ V′ U′)
      (suc index)) →
  (∀ {W W′ A A′ B B′ V V′ U U′}
      {R : WorldRelation W W′} →
    (value : OperationalValueNarrowing
      (A ⇒ᵛ B) (A′ ⇒ᵛ B′) R V V′) →
    QuotientOperationalOrigin (operational-origin value) →
    OperationalValueNarrowing A A′ R U U′ →
    BackwardReturnSimulation
      (OperationalValueResult B B′) R
      (applyValue W V U) (applyValue W′ V′ U′)
      (suc index)
    ×
    TargetBlameSimulation R
      (applyValue W V U) (applyValue W′ V′ U′)
      (suc index)) →
  ∀ {W W′ A A′ B B′ V V′ U U′}
    {R : WorldRelation W W′} →
  OperationalValueNarrowing
    (A ⇒ᵛ B) (A′ ⇒ᵛ B′) R V V′ →
  OperationalValueNarrowing A A′ R U U′ →
  BackwardReturnSimulation
    (OperationalValueResult B B′) R
    (applyValue W V U) (applyValue W′ V′ U′)
    (suc index)
  ×
  TargetBlameSimulation R
    (applyValue W V U) (applyValue W′ V′ U′)
    (suc index)
directional-operational-apply-backward-result-positive
    {index} term-simulation coercion application
    left-coercion left-application instantiated quotient
    (operational-value typed
      (closure-origin runtime environment origins terms))
    argument =
  closure-application-backward
    {index = index}
    term-simulation runtime environment origins terms argument
directional-operational-apply-backward-result-positive
    {index} term-simulation coercion application
    left-coercion left-application instantiated quotient
    (operational-value typed
      (paired-function-origin runtime action domain codomain value))
    argument =
  backward-return proxy , target-blame-reflects proxy
  where
  components =
    paired-conversion-function-components-reachable action

  proxy =
    paired-function-proxy-backward-bundle {index = index}
      (proj₁ coercion runtime (proj₁ components) argument)
      (proj₂ coercion runtime (proj₁ components) argument)
      (λ R≤S domain-value →
        proj₁ application
          (operational-value-narrowing-weaken R≤S
            (left-world-typed (operational-typed domain-value))
            (right-world-typed (operational-typed domain-value))
            value)
          domain-value)
      (λ R≤S domain-value →
        proj₂ application
          (operational-value-narrowing-weaken R≤S
            (left-world-typed (operational-typed domain-value))
            (right-world-typed (operational-typed domain-value))
            value)
          domain-value)
      (λ R≤S application-value →
        proj₁ coercion
          (runtime-narrowing-weaken R≤S
            (left-world-typed (operational-typed application-value))
            (right-world-typed (operational-typed application-value))
            runtime)
          (proj₂ components) application-value)
      (λ R≤S application-value →
        proj₂ coercion
          (runtime-narrowing-weaken R≤S
            (left-world-typed (operational-typed application-value))
            (right-world-typed (operational-typed application-value))
            runtime)
          (proj₂ components) application-value)
directional-operational-apply-backward-result-positive
    {index} term-simulation coercion application
    left-coercion left-application instantiated quotient
    (operational-value typed
      (left-function-origin
        {V = V₀} {V′ = V₀′}
        runtime action domain codomain value))
    argument =
  backward-return proxy , target-blame-reflects proxy
  where
  proxy =
    left-function-proxy-backward-bundle
      {V = V₀} {V′ = V₀′} {index = suc index}
      (proj₁ left-coercion runtime
        (left-component-reachable domain) argument)
      (proj₂ left-coercion runtime
        (left-component-reachable domain) argument)
      (λ R≤S domain-value →
        proj₁ left-application
          (operational-value-narrowing-weaken R≤S
            (left-world-typed (operational-typed domain-value))
            (right-world-typed (operational-typed domain-value))
            value)
          domain-value)
      (λ R≤S domain-value →
        proj₂ left-application
          (operational-value-narrowing-weaken R≤S
            (left-world-typed (operational-typed domain-value))
            (right-world-typed (operational-typed domain-value))
            value)
          domain-value)
      (λ R≤S application-value →
        proj₁ left-coercion
          (runtime-narrowing-weaken R≤S
            (left-world-typed (operational-typed application-value))
            (right-world-typed (operational-typed application-value))
            runtime)
          (left-component-reachable codomain) application-value)
      (λ R≤S application-value →
        proj₂ left-coercion
          (runtime-narrowing-weaken R≤S
            (left-world-typed (operational-typed application-value))
            (right-world-typed (operational-typed application-value))
            runtime)
          (left-component-reachable codomain) application-value)
directional-operational-apply-backward-result-positive
    {index} term-simulation coercion application
    left-coercion left-application instantiated quotient
    (operational-value typed
      (right-function-components-origin
        runtime action domain codomain value))
    argument =
  backward-return proxy , target-blame-reflects proxy
  where
  proxy =
    right-function-proxy-backward-bundle {index = index}
      (proj₁ coercion runtime
        (right-component-reachable domain) argument)
      (proj₂ coercion runtime
        (right-component-reachable domain) argument)
      (λ R≤S domain-value →
        proj₁ application
          (operational-value-narrowing-weaken R≤S
            (left-world-typed (operational-typed domain-value))
            (right-world-typed (operational-typed domain-value))
            value)
          domain-value)
      (λ R≤S domain-value →
        proj₂ application
          (operational-value-narrowing-weaken R≤S
            (left-world-typed (operational-typed domain-value))
            (right-world-typed (operational-typed domain-value))
            value)
          domain-value)
      (λ R≤S application-value →
        proj₁ coercion
          (runtime-narrowing-weaken R≤S
            (left-world-typed (operational-typed application-value))
            (right-world-typed (operational-typed application-value))
            runtime)
          (right-component-reachable codomain) application-value)
      (λ R≤S application-value →
        proj₂ coercion
          (runtime-narrowing-weaken R≤S
            (left-world-typed (operational-typed application-value))
            (right-world-typed (operational-typed application-value))
            runtime)
          (right-component-reachable codomain) application-value)
directional-operational-apply-backward-result-positive
    {index} term-simulation coercion application
    left-coercion left-application instantiated quotient
    (operational-value typed
      (right-function-origin runtime action value))
    argument
    with right-function-coercion-components action
directional-operational-apply-backward-result-positive
    {index} term-simulation coercion application
    left-coercion left-application instantiated quotient
    (operational-value typed
      (right-function-origin runtime action value))
    argument
    | domain , codomain =
  directional-operational-apply-backward-result-positive
    term-simulation coercion application
    left-coercion left-application instantiated quotient
    (operational-value typed
      (right-function-components-origin
        runtime action domain codomain value))
    argument
directional-operational-apply-backward-result-positive
    {index} term-simulation coercion application
    left-coercion left-application instantiated quotient
    (operational-value typed
      (right-function-boundary-origin
        runtime action origin-value left-eq))
    argument
    with right-boundary-function-coercion-components left-eq action
directional-operational-apply-backward-result-positive
    {index} term-simulation coercion application
    left-coercion left-application instantiated quotient
    (operational-value typed
      (right-function-boundary-origin
        runtime action origin-value left-eq))
    argument
    | S₁ , S₂ , A₁′ , B₁′ , pA , pB , pC , pD ,
      refl , refl , refl , domain , codomain =
  backward-return proxy , target-blame-reflects proxy
  where
  proxy =
    right-function-proxy-backward-bundle {index = index}
      (proj₁ coercion runtime
        (right-component-reachable domain) argument)
      (proj₂ coercion runtime
        (right-component-reachable domain) argument)
      (λ R≤S domain-value →
        proj₁ application
          (operational-value-narrowing-weaken R≤S
            (left-world-typed (operational-typed domain-value))
            (right-world-typed (operational-typed domain-value))
            (operational-value-type-transport
              (sym left-eq) refl origin-value))
          domain-value)
      (λ R≤S domain-value →
        proj₂ application
          (operational-value-narrowing-weaken R≤S
            (left-world-typed (operational-typed domain-value))
            (right-world-typed (operational-typed domain-value))
            (operational-value-type-transport
              (sym left-eq) refl origin-value))
          domain-value)
      (λ R≤S application-value →
        proj₁ coercion
          (runtime-narrowing-weaken R≤S
            (left-world-typed (operational-typed application-value))
            (right-world-typed (operational-typed application-value))
            runtime)
          (right-component-reachable codomain) application-value)
      (λ R≤S application-value →
        proj₂ coercion
          (runtime-narrowing-weaken R≤S
            (left-world-typed (operational-typed application-value))
            (right-world-typed (operational-typed application-value))
            runtime)
          (right-component-reachable codomain) application-value)
directional-operational-apply-backward-result-positive
    {index} term-simulation coercion application
    left-coercion left-application instantiated quotient
    value@(operational-value typed
      (left-name-instantiated-origin R≤S α-ok result-eq origin-value))
    argument =
  instantiated value name-instantiated-operational-origin argument
directional-operational-apply-backward-result-positive
    {index} term-simulation coercion application
    left-coercion left-application instantiated quotient
    value@(operational-value typed
      (operational-quotient-origin
        runtime D⊑E alignment down up left-eq right-eq
        frame origin-value))
    argument =
  quotient value active-quotient-operational-origin argument
directional-operational-apply-backward-result-positive
    {index} term-simulation coercion application
    left-coercion left-application instantiated quotient
    value@(operational-value typed
      (quotient-origin runtime base terms left-eq right-eq
        frame origin-value))
    argument =
  quotient value quotient-operational-origin argument


directional-operational-apply-backward-positive :
  ∀ {index} →
  (∀ {Φ Δᴸ Δᴿ ρ γᵀ N N′ A B p} →
    FramedDirectionalInterpreterTermSimulation
      backward-direction index Φ Δᴸ Δᴿ ρ γᵀ N N′ A B p
    ×
    FramedDirectionalInterpreterTermSimulation
      target-blame-direction index Φ Δᴸ Δᴿ ρ γᵀ N N′ A B p) →
  (DirectionalCoercionSimulation backward-direction index
   × DirectionalCoercionSimulation target-blame-direction index) →
  (DirectionalApplyValueSimulation backward-direction index
   × DirectionalApplyValueSimulation target-blame-direction index) →
  (DirectionalCoercionSimulation backward-direction (suc index)
   ×
   DirectionalCoercionSimulation
     target-blame-direction (suc index)) →
  (DirectionalApplyValueSimulation backward-direction (suc index)
   ×
   DirectionalApplyValueSimulation
     target-blame-direction (suc index)) →
  (∀ {W W′ A A′ B B′ V V′ U U′}
      {R : WorldRelation W W′} →
    (value : OperationalValueNarrowing
      (A ⇒ᵛ B) (A′ ⇒ᵛ B′) R V V′) →
    NameInstantiatedOperationalOrigin (operational-origin value) →
    OperationalValueNarrowing A A′ R U U′ →
    BackwardReturnSimulation
      (OperationalValueResult B B′) R
      (applyValue W V U) (applyValue W′ V′ U′)
      (suc index)
    ×
    TargetBlameSimulation R
      (applyValue W V U) (applyValue W′ V′ U′)
      (suc index)) →
  (∀ {W W′ A A′ B B′ V V′ U U′}
      {R : WorldRelation W W′} →
    (value : OperationalValueNarrowing
      (A ⇒ᵛ B) (A′ ⇒ᵛ B′) R V V′) →
    QuotientOperationalOrigin (operational-origin value) →
    OperationalValueNarrowing A A′ R U U′ →
    BackwardReturnSimulation
      (OperationalValueResult B B′) R
      (applyValue W V U) (applyValue W′ V′ U′)
      (suc index)
    ×
    TargetBlameSimulation R
      (applyValue W V U) (applyValue W′ V′ U′)
      (suc index)) →
  (DirectionalApplyValueSimulation
      backward-direction (suc index)
   ×
   DirectionalApplyValueSimulation
      target-blame-direction (suc index))
directional-operational-apply-backward-positive
    term-simulation coercion application
    left-coercion left-application instantiated quotient =
  (λ value argument {U′} {V′} result-eq →
    proj₁
      (directional-operational-apply-backward-result-positive
        term-simulation coercion application
        left-coercion left-application instantiated quotient
        value argument)
      result-eq) ,
  (λ value argument {U′} result-eq →
    proj₂
      (directional-operational-apply-backward-result-positive
        term-simulation coercion application
        left-coercion left-application instantiated quotient
        value argument)
      result-eq)

module proof.InterpreterDirectionalFramedApplyBackward where

-- File Charter:
--   * Dispatches positive-fuel backward-return and target-blame application
--     observations together over exact framed origins.
--   * Sends paired widenings and quotient functions to one exact-origin
--     callback, so unsafe covariant components never escape independently.
--   * Keeps the two mutually supporting target-directed observations paired.
--   * Contains no small-step reduction or catch-up theorem.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (_∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (sym)

open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import Interpreter
open import Simulation.Coercion.InterpreterCoercionComponents
open import Simulation.Directional.InterpreterDirectionalSimulationMotive
open import Narrowing.InterpreterFramedValueNarrowing
open import Narrowing.InterpreterFramedValueNarrowingProperties
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Narrowing.InterpreterOperationalValueNarrowing
open import Narrowing.InterpreterReachableCoercionNarrowing using
  ( left-component-reachable
  ; paired-conversion-function-components-reachable
  ; right-component-reachable
  )
open import Typing.InterpreterSemanticTypingCore using
  (environment-cons; ⟦_⟧[_])
open import Simulation.Core.InterpreterSimulationContext
open import Simulation.Core.InterpreterSimulationResult using (guard)
open import Narrowing.InterpreterTermNarrowing
open import Narrowing.InterpreterTypedValueNarrowing using
  ( TypedValueNarrowing
  ; left-value-typed
  ; right-value-typed
  ; values-narrow
  )
import NuTermImprecision as NTI
import NuTerms as N
open import
  proof.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import proof.InterpreterDirectionalCompilerReplanning using
  ( compiler-replanned-application-backward
  ; compiler-replanned-application-target-blame
  )
open import proof.InterpreterDirectionalFraming using
  (operational-backward-to-framed)
open import proof.InterpreterDirectionalFunctionProxy using
  ( left-function-proxy-backward-bundle
  ; paired-function-proxy-backward-bundle
  ; right-function-proxy-backward-bundle
  )
open import proof.InterpreterDirectionalGuard using
  (paired-guard-backward; paired-guard-target-blame)
open import proof.InterpreterDirectionalTransport using
  (backward-pointwise; target-blame-pointwise)
open import Types

open Narrowing.InterpreterTermNarrowing.RelatedWorlds
open Narrowing.InterpreterTermNarrowing.InterpreterValues

closure-application-computation :
  ∀ {W N γ θ U} n →
  applyValue W (closure N γ θ) U n ≡
  guard W (interpret W (U ∷ γ) θ N) n
closure-application-computation zero =
  refl
closure-application-computation (suc n) =
  refl

operational-application-framed-backward :
  ∀ {index W W′ Φ Δᴸ Δᴿ}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {θ θ′ A A′ B B′ V V′ U U′}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {R : WorldRelation W W′} →
  DirectionalApplyValueSimulation backward-direction index →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  FramedValueNarrowing
    {A = A ⇒ B} {A′ = A′ ⇒ B′}
    {p = pA ImprecisionWf.↦ pB} runtime V V′ →
  FramedValueNarrowing
    {A = A} {A′ = A′} {p = pA} runtime U U′ →
  BackwardReturnSimulation
    (FramedValueResult ρ θ θ′ pB) R
    (applyValue W V U) (applyValue W′ V′ U′) index
operational-application-framed-backward
    {index} {W} {W′} {Φ} {Δᴸ} {Δᴿ}
    {ρ} {θ} {θ′} {A} {A′} {B} {B′}
    {V} {V′} {U} {U′} {pA} {pB} {R}
    application runtime value argument =
  operational-backward-to-framed
    {W = W} {W′ = W′} {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {right-index = index} {ρ = ρ} {θ = θ} {θ′ = θ′}
    {A = B} {A′ = B′} {p = pB} {R = R}
    {left = applyValue W V U}
    {right = applyValue W′ V′ U′}
    runtime
    (application {W = W} {W′ = W′}
      {A = ⟦ A ⟧[ θ ]} {A′ = ⟦ A′ ⟧[ θ′ ]}
      {B = ⟦ B ⟧[ θ ]} {B′ = ⟦ B′ ⟧[ θ′ ]}
      {V = V} {V′ = V′} {U = U} {U′ = U′} {R = R}
      (framed-value-operational value)
      (framed-value-operational argument))

closure-application-framed-backward :
  ∀ {index W W′ Φ Δᴸ Δᴿ}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {γᵀ : NTI.CtxImp Φ Δᴸ Δᴿ}
    {θ θ′ γ γ′ N N′ A A′ B B′ U U′}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {R : WorldRelation W W′} →
  (FramedDirectionalInterpreterTermSimulation
     backward-direction index Φ Δᴸ Δᴿ ρ
     (NTI.ctx-imp A A′ pA ∷ γᵀ) N N′ B B′ pB
   ×
   FramedDirectionalInterpreterTermSimulation
     target-blame-direction index Φ Δᴸ Δᴿ ρ
     (NTI.ctx-imp A A′ pA ∷ γᵀ) N N′ B B′ pB) →
  AssumptionMembershipUnique Φ →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  EnvironmentRealization runtime γᵀ γ γ′ →
  FramedEnvironmentNarrowing runtime γᵀ γ γ′ →
  OpenInterpreterTermNarrowing R Φ Δᴸ Δᴿ ρ
    (NTI.ctx-imp A A′ pA ∷ γᵀ) N N′ B B′ pB →
  FramedValueNarrowing
    {A = A} {A′ = A′} {p = pA} runtime U U′ →
  BackwardReturnSimulation
    (FramedValueResult ρ θ θ′ pB) R
    (applyValue W (closure N γ θ) U)
    (applyValue W′ (closure N′ γ′ θ′) U′)
    (suc index)
  ×
  TargetBlameSimulation R
    (applyValue W (closure N γ θ) U)
    (applyValue W′ (closure N′ γ′ θ′) U′)
    (suc index)
closure-application-framed-backward
    {index} {W} {W′} {Φ} {Δᴸ} {Δᴿ}
    {ρ} {γᵀ} {θ} {θ′} {γ} {γ′} {N} {N′}
    {A} {A′} {B} {B′} {U} {U′} {pA} {pB} {R}
    term-simulation unique runtime environment origins terms argument =
  backward-pointwise
    {W = W} {W′ = W′} {right-index = suc index}
    {value-result = FramedValueResult ρ θ θ′ pB} {R = R}
    {left = guard W (interpret W (U ∷ γ) θ N)}
    {left′ = applyValue W (closure N γ θ) U}
    {right = guard W′ (interpret W′ (U′ ∷ γ′) θ′ N′)}
    {right′ = applyValue W′ (closure N′ γ′ θ′) U′}
    (λ n → sym (closure-application-computation n))
    (λ n → sym (closure-application-computation n))
    guarded-backward ,
  target-blame-pointwise
    {W = W} {W′ = W′} {right-index = suc index} {R = R}
    {left = guard W (interpret W (U ∷ γ) θ N)}
    {left′ = applyValue W (closure N γ θ) U}
    {right = guard W′ (interpret W′ (U′ ∷ γ′) θ′ N′)}
    {right′ = applyValue W′ (closure N′ γ′ θ′) U′}
    (λ n → sym (closure-application-computation n))
    (λ n → sym (closure-application-computation n))
    guarded-blame
  where
  environment′ =
    environment-realization
      (values-narrow (framed-value-typed argument) ∷⊑∷ᵉ
       environments-narrow environment)
      (environment-cons
        (left-value-typed (framed-value-typed argument))
        (left-environment-typed environment))
      (environment-cons
        (right-value-typed (framed-value-typed argument))
        (right-environment-typed environment))

  origins′ = argument ∷⊑∷ᶠ origins

  body-backward :
    BackwardReturnSimulation
      (FramedValueResult ρ θ θ′ pB) R
      (interpret W (U ∷ γ) θ N)
      (interpret W′ (U′ ∷ γ′) θ′ N′) index
  body-backward =
    proj₁ term-simulation unique runtime environment′ origins′ terms

  body-blame :
    TargetBlameSimulation R
      (interpret W (U ∷ γ) θ N)
      (interpret W′ (U′ ∷ γ′) θ′ N′) index
  body-blame =
    proj₂ term-simulation unique runtime environment′ origins′ terms

  guarded-backward :
    BackwardReturnSimulation
      (FramedValueResult ρ θ θ′ pB) R
      (guard W (interpret W (U ∷ γ) θ N))
      (guard W′ (interpret W′ (U′ ∷ γ′) θ′ N′))
      (suc index)
  guarded-backward =
    paired-guard-backward
      {W = W} {W′ = W′} {U = W} {U′ = W′}
      {right-index = index}
      {value-result = FramedValueResult ρ θ θ′ pB}
      {R = R}
      {left = interpret W (U ∷ γ) θ N}
      {right = interpret W′ (U′ ∷ γ′) θ′ N′}
      refl body-backward body-blame

  guarded-blame :
    TargetBlameSimulation R
      (guard W (interpret W (U ∷ γ) θ N))
      (guard W′ (interpret W′ (U′ ∷ γ′) θ′ N′))
      (suc index)
  guarded-blame =
    paired-guard-target-blame
      {W = W} {W′ = W′} {U = W} {U′ = W′}
      {right-index = index}
      {value-result = FramedValueResult ρ θ θ′ pB}
      {R = R}
      {left = interpret W (U ∷ γ) θ N}
      {right = interpret W′ (U′ ∷ γ′) θ′ N′}
      refl body-backward body-blame

directional-framed-apply-backward-positive :
  ∀ {index} →
  (∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
      {γᵀ : NTI.CtxImp Φ Δᴸ Δᴿ}
      {N N′ : N.Term} {A B : Ty}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    FramedDirectionalInterpreterTermSimulation
      backward-direction index Φ Δᴸ Δᴿ ρ γᵀ N N′ A B p
    ×
    FramedDirectionalInterpreterTermSimulation
      target-blame-direction index Φ Δᴸ Δᴿ ρ γᵀ N N′ A B p) →
  (FramedDirectionalCoercionSimulation backward-direction index
   × FramedDirectionalCoercionSimulation target-blame-direction index) →
  (FramedDirectionalApplyValueSimulation backward-direction index
   × FramedDirectionalApplyValueSimulation
       target-blame-direction index) →
  (FramedDirectionalCoercionSimulation
       backward-direction (suc index)
   × FramedDirectionalCoercionSimulation
       target-blame-direction (suc index)) →
  (FramedDirectionalApplyValueSimulation
       backward-direction (suc index)
   × FramedDirectionalApplyValueSimulation
       target-blame-direction (suc index)) →
  (DirectionalApplyValueSimulation backward-direction (suc index)
   × DirectionalApplyValueSimulation
       target-blame-direction (suc index)) →
  (∀ {W W′ Φ Δᴸ Δᴿ}
      {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
      {θ θ′ A A′ B B′ V V′ U U′}
      {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
      {R : WorldRelation W W′}
      {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
    AssumptionMembershipUnique Φ →
    (value : FramedValueNarrowing
      {A = A ⇒ B} {A′ = A′ ⇒ B′}
      {p = pA ImprecisionWf.↦ pB} runtime V V′) →
    NameInstantiatedFramedValue value →
    FramedValueNarrowing
      {A = A} {A′ = A′} {p = pA} runtime U U′ →
    BackwardReturnSimulation
      (FramedValueResult ρ θ θ′ pB) R
      (applyValue W V U) (applyValue W′ V′ U′)
      (suc index)
    ×
    TargetBlameSimulation R
      (applyValue W V U) (applyValue W′ V′ U′)
      (suc index)) →
  (∀ {W W′ Φ Δᴸ Δᴿ}
      {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
      {θ θ′ A A′ B B′ V V′ U U′}
      {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
      {R : WorldRelation W W′} →
    AssumptionMembershipUnique Φ →
    (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
    TypedValueNarrowing
      ⟦ A ⇒ B ⟧[ θ ] ⟦ A′ ⇒ B′ ⟧[ θ′ ] R V V′ →
    FramedValueOrigin runtime
      (pA ImprecisionWf.↦ pB) V V′ →
    FramedValueNarrowing
      {A = A} {A′ = A′} {p = pA} runtime U U′ →
    BackwardReturnSimulation
      (FramedValueResult ρ θ θ′ pB) R
      (applyValue W V U) (applyValue W′ V′ U′)
      (suc index)
    ×
    TargetBlameSimulation R
      (applyValue W V U) (applyValue W′ V′ U′)
      (suc index)) →
  ∀ {W W′ Φ Δᴸ Δᴿ}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {θ θ′ A A′ B B′ V V′ U U′}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {R : WorldRelation W W′} →
  AssumptionMembershipUnique Φ →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  FramedValueNarrowing
    {A = A ⇒ B} {A′ = A′ ⇒ B′}
    {p = pA ImprecisionWf.↦ pB} runtime V V′ →
  FramedValueNarrowing
    {A = A} {A′ = A′} {p = pA} runtime U U′ →
  BackwardReturnSimulation
    (FramedValueResult ρ θ θ′ pB) R
    (applyValue W V U) (applyValue W′ V′ U′)
    (suc index)
  ×
  TargetBlameSimulation R
    (applyValue W V U) (applyValue W′ V′ U′)
    (suc index)
directional-framed-apply-backward-positive
    {index} term-simulation coercion application
    left-coercion left-application operational-application
    name-simulation quotient-simulation unique runtime
    (framed-value typed operational
      (closure-originᶠ environment origins terms))
    argument =
  closure-application-framed-backward
    {index = index}
    term-simulation unique runtime environment origins terms argument
directional-framed-apply-backward-positive
    {index} term-simulation coercion application
    left-coercion left-application operational-application
    name-simulation quotient-simulation unique runtime
    (framed-value typed operational
      origin@(paired-function-originᶠ action domain codomain value))
    argument =
  backward-return proxy , target-blame-reflects proxy
  where
  components =
    paired-conversion-function-components-reachable action

  proxy =
    paired-function-proxy-backward-bundle {index = index}
      (proj₁ coercion unique runtime
        (proj₁ components) argument)
      (proj₂ coercion unique runtime
        (proj₁ components) argument)
      (λ
        { R≤S (framed-result runtimeS domain-value) →
            proj₁ application unique runtimeS
              (framed-value-narrowing-future R≤S value)
              domain-value
        })
      (λ
        { R≤S (framed-result runtimeS domain-value) →
            proj₂ application unique runtimeS
              (framed-value-narrowing-future R≤S value)
              domain-value
        })
      (λ
        { R≤S (framed-result runtimeS application-value) →
            proj₁ coercion unique runtimeS
              (proj₂ components) application-value
        })
      (λ
        { R≤S (framed-result runtimeS application-value) →
            proj₂ coercion unique runtimeS
              (proj₂ components) application-value
        })
directional-framed-apply-backward-positive
    {index} term-simulation coercion application
    left-coercion left-application operational-application
    name-simulation quotient-simulation unique runtime
    (framed-value typed operational
      (left-function-originᶠ
        {θ = θ} {c = c} {d = d}
        {V = base} {V′ = base′}
        action domain codomain value))
    argument =
  backward-return proxy , target-blame-reflects proxy
  where
  proxy =
    left-function-proxy-backward-bundle
      {θ = θ} {p = c} {q = d}
      {V = base} {V′ = base′} {index = suc index}
      (proj₁ left-coercion unique runtime
        (left-component-reachable domain) argument)
      (proj₂ left-coercion unique runtime
        (left-component-reachable domain) argument)
      (λ
        { R≤S (framed-result runtimeS domain-value) →
            proj₁ left-application unique runtimeS
              (framed-value-narrowing-future R≤S value)
              domain-value
        })
      (λ
        { R≤S (framed-result runtimeS domain-value) →
            proj₂ left-application unique runtimeS
              (framed-value-narrowing-future R≤S value)
              domain-value
        })
      (λ
        { R≤S (framed-result runtimeS application-value) →
            proj₁ left-coercion unique runtimeS
              (left-component-reachable codomain) application-value
        })
      (λ
        { R≤S (framed-result runtimeS application-value) →
            proj₂ left-coercion unique runtimeS
              (left-component-reachable codomain) application-value
        })
directional-framed-apply-backward-positive
    {index} term-simulation coercion application
    left-coercion left-application operational-application
    name-simulation quotient-simulation unique runtime
    (framed-value typed operational
      (right-function-originᶠ action domain codomain value))
    argument =
  backward-return proxy , target-blame-reflects proxy
  where
  proxy =
    right-function-proxy-backward-bundle {index = index}
      (proj₁ coercion unique runtime
        (right-component-reachable domain) argument)
      (proj₂ coercion unique runtime
        (right-component-reachable domain) argument)
      (λ
        { R≤S (framed-result runtimeS domain-value) →
            proj₁ application unique runtimeS
              (framed-value-narrowing-future R≤S value)
              domain-value
        })
      (λ
        { R≤S (framed-result runtimeS domain-value) →
            proj₂ application unique runtimeS
              (framed-value-narrowing-future R≤S value)
              domain-value
        })
      (λ
        { R≤S (framed-result runtimeS application-value) →
            proj₁ coercion unique runtimeS
              (right-component-reachable codomain) application-value
        })
      (λ
        { R≤S (framed-result runtimeS application-value) →
            proj₂ coercion unique runtimeS
              (right-component-reachable codomain) application-value
        })
directional-framed-apply-backward-positive
    {index} term-simulation coercion application
    left-coercion left-application operational-application
    name-simulation quotient-simulation unique runtime
    value@(reframed-value typed inner)
    argument =
  operational-application-framed-backward
    {index = suc index}
    (proj₁ operational-application) runtime value argument ,
  proj₂ operational-application
    (framed-value-operational value)
    (framed-value-operational argument)
directional-framed-apply-backward-positive
    {index} term-simulation coercion application
    left-coercion left-application operational-application
    name-simulation quotient-simulation unique runtime
    value@(reindexed-value typed inner)
    argument =
  operational-application-framed-backward
    {index = suc index}
    (proj₁ operational-application) runtime value argument ,
  proj₂ operational-application
    (framed-value-operational value)
    (framed-value-operational argument)
directional-framed-apply-backward-positive
    {index} term-simulation coercion application
    left-coercion left-application operational-application
    name-simulation quotient-simulation unique runtime
    value@(left-name-instantiated-value
      typed operational R≤S α-ok result-eq inner)
    argument =
  name-simulation unique value
    name-instantiated-framed-value argument
directional-framed-apply-backward-positive
    {index} term-simulation coercion application
    left-coercion left-application operational-application
    name-simulation quotient-simulation unique runtime
    value@(operationally-framed-value operational)
    argument =
  operational-application-framed-backward
    {index = suc index}
    (proj₁ operational-application) runtime value argument ,
  proj₂ operational-application
    (framed-value-operational value)
    (framed-value-operational argument)
directional-framed-apply-backward-positive
    {index} term-simulation coercion application
    left-coercion left-application operational-application
    name-simulation quotient-simulation unique runtime
    value@(compiler-replanned-value typed operational inner)
    argument =
  compiler-replanned-application-backward
    {index = suc index}
    (proj₁ left-application) unique inner argument ,
  compiler-replanned-application-target-blame
    {index = suc index}
    (proj₂ left-application) unique inner argument
directional-framed-apply-backward-positive
    {index} term-simulation coercion application
    left-coercion left-application operational-application
    name-simulation quotient-simulation unique runtime
    value@(paired-lifted-value
      unique₀ left-eq right-eq R≤S typed operational inner)
    argument =
  operational-application-framed-backward
    {index = suc index}
    (proj₁ operational-application) runtime value argument ,
  proj₂ operational-application
    (framed-value-operational value)
    (framed-value-operational argument)
directional-framed-apply-backward-positive
    {index} term-simulation coercion application
    left-coercion left-application operational-application
    name-simulation quotient-simulation unique runtime
    value@(paired-unlifted-value
      unique₀ typed operational inner)
    argument =
  operational-application-framed-backward
    {index = suc index}
    (proj₁ operational-application) runtime value argument ,
  proj₂ operational-application
    (framed-value-operational value)
    (framed-value-operational argument)
directional-framed-apply-backward-positive
    {index} term-simulation coercion application
    left-coercion left-application operational-application
    name-simulation quotient-simulation unique runtime
    value@(left-lifted-value
      unique₀ left-eq R≤S typed operational inner)
    argument =
  operational-application-framed-backward
    {index = suc index}
    (proj₁ operational-application) runtime value argument ,
  proj₂ operational-application
    (framed-value-operational value)
    (framed-value-operational argument)
directional-framed-apply-backward-positive
    {index} term-simulation coercion application
    left-coercion left-application operational-application
    name-simulation quotient-simulation unique runtime
    value@(left-unlifted-value
      unique₀ typed operational inner)
    argument =
  operational-application-framed-backward
    {index = suc index}
    (proj₁ operational-application) runtime value argument ,
  proj₂ operational-application
    (framed-value-operational value)
    (framed-value-operational argument)
directional-framed-apply-backward-positive
    {index} term-simulation coercion application
    left-coercion left-application operational-application
    name-simulation quotient-simulation unique runtime
    (framed-value typed operational
      origin@(operational-quotient-originᶠ
        D⊑E alignment down up frame value))
    argument =
  quotient-simulation unique runtime typed origin argument
directional-framed-apply-backward-positive
    {index} term-simulation coercion application
    left-coercion left-application operational-application
    name-simulation quotient-simulation unique runtime
    (framed-value typed operational
      origin@(quotient-originᶠ base terms frame value))
    argument =
  quotient-simulation unique runtime typed origin argument

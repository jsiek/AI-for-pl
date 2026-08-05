module proof.InterpreterDirectionalFraming where

-- File Charter:
--   * Erases exact framed returned values to operational origins and restores
--     operational results under the uniquely weakened runtime frame.
--   * Provides the conversion separately for forward and backward return;
--     target blame carries no returned value and needs no conversion.
--   * Contains no interpreter recursion, reduction, or catch-up theorem.

open import ImprecisionWf using (_∣_⊢_⊑_⊣_)

open import Interpreter
open import Simulation.Directional.InterpreterDirectionalSimulationMotive
open import Simulation.Coercion.InterpreterCoercionSimulationMotive using
  (executeCoercionAction)
open import Narrowing.InterpreterFramedValueNarrowing
open import Narrowing.InterpreterFramedValueNarrowingProperties
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Narrowing.InterpreterOperationalValueNarrowing
open import Narrowing.InterpreterOperationalValueNarrowingProperties
open import Narrowing.InterpreterReachableCoercionNarrowing
open import Typing.InterpreterSemanticTypingCore using (⟦_⟧[_])
open import Simulation.Core.InterpreterSimulationContext
open import Simulation.Core.InterpreterSimulationContextProperties using
  (runtime-narrowing-weaken)
open import Narrowing.InterpreterTermNarrowing
open import Narrowing.InterpreterTypedValueNarrowing using
  (left-world-typed; right-world-typed)
import NuTermImprecision as NTI
import NuTerms as N
open import
  proof.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import proof.InterpreterDirectionalTransport using
  (backward-result-map; forward-result-map)
open import Types

open Narrowing.InterpreterTermNarrowing.RelatedWorlds

framed-forward-to-operational :
  ∀ {W W′ Φ Δᴸ Δᴿ left-index}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {θ θ′ A A′}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {R : WorldRelation W W′}
    {left right} →
  ForwardReturnSimulation
    (FramedValueResult ρ θ θ′ p) R left right left-index →
  ForwardReturnSimulation
    (OperationalValueResult ⟦ A ⟧[ θ ] ⟦ A′ ⟧[ θ′ ])
    R left right left-index
framed-forward-to-operational
    {left-index = left-index} {ρ = ρ}
    {θ = θ} {θ′} {A} {A′} {p} {R} {left} {right}
    simulation =
  forward-result-map
    {left-index = left-index}
    {source-result = FramedValueResult ρ θ θ′ p}
    {target-result =
      OperationalValueResult ⟦ A ⟧[ θ ] ⟦ A′ ⟧[ θ′ ]}
    {R = R} {left = left} {right = right}
    simulation
    (λ
      { R≤S (framed-result runtime value) →
          framed-value-operational value
      })

framed-backward-to-operational :
  ∀ {W W′ Φ Δᴸ Δᴿ right-index}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {θ θ′ A A′}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {R : WorldRelation W W′}
    {left right} →
  BackwardReturnSimulation
    (FramedValueResult ρ θ θ′ p) R left right right-index →
  BackwardReturnSimulation
    (OperationalValueResult ⟦ A ⟧[ θ ] ⟦ A′ ⟧[ θ′ ])
    R left right right-index
framed-backward-to-operational
    {right-index = right-index} {ρ = ρ}
    {θ = θ} {θ′} {A} {A′} {p} {R} {left} {right}
    simulation =
  backward-result-map
    {right-index = right-index}
    {source-result = FramedValueResult ρ θ θ′ p}
    {target-result =
      OperationalValueResult ⟦ A ⟧[ θ ] ⟦ A′ ⟧[ θ′ ]}
    {R = R} {left = left} {right = right}
    simulation
    (λ
      { R≤S (framed-result runtime value) →
          framed-value-operational value
      })


framed-coercion-forward-to-operational :
  ∀ {index} →
  FramedDirectionalCoercionSimulation forward-direction index →
  DirectionalCoercionSimulation forward-direction index
framed-coercion-forward-to-operational
    {index} simulation
    {W} {W′} {Φ} {Δᴸ} {Δᴿ} {ρ} {θ} {θ′}
    {A} {A′} {B} {B′} {p} {q} {V} {V′}
    {left} {right} {R} runtime action value =
  framed-forward-to-operational
    {W = W} {W′ = W′} {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {left-index = index} {ρ = ρ} {θ = θ} {θ′ = θ′}
    {A = B} {A′ = B′} {p = q} {R = R}
    {left = executeCoercionAction W θ left V}
    {right = executeCoercionAction W′ θ′ right V′}
    (simulation
      (assumption-membership-unique runtime)
      runtime action
      (operationally-framed-value value))


framed-coercion-backward-to-operational :
  ∀ {index} →
  FramedDirectionalCoercionSimulation backward-direction index →
  DirectionalCoercionSimulation backward-direction index
framed-coercion-backward-to-operational
    {index} simulation
    {W} {W′} {Φ} {Δᴸ} {Δᴿ} {ρ} {θ} {θ′}
    {A} {A′} {B} {B′} {p} {q} {V} {V′}
    {left} {right} {R} runtime action value =
  framed-backward-to-operational
    {W = W} {W′ = W′} {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {right-index = index} {ρ = ρ} {θ = θ} {θ′ = θ′}
    {A = B} {A′ = B′} {p = q} {R = R}
    {left = executeCoercionAction W θ left V}
    {right = executeCoercionAction W′ θ′ right V′}
    (simulation
      (assumption-membership-unique runtime)
      runtime action
      (operationally-framed-value value))


framed-coercion-target-blame-to-operational :
  ∀ {index} →
  FramedDirectionalCoercionSimulation
    target-blame-direction index →
  DirectionalCoercionSimulation target-blame-direction index
framed-coercion-target-blame-to-operational
    simulation runtime action value =
  simulation
    (assumption-membership-unique runtime)
    runtime action
    (operationally-framed-value value)

operational-forward-to-framed :
  ∀ {W W′ Φ Δᴸ Δᴿ left-index}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {θ θ′ A A′}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {R : WorldRelation W W′}
    {left right} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  ForwardReturnSimulation
    (OperationalValueResult ⟦ A ⟧[ θ ] ⟦ A′ ⟧[ θ′ ])
    R left right left-index →
  ForwardReturnSimulation
    (FramedValueResult ρ θ θ′ p) R left right left-index
operational-forward-to-framed
    {left-index = left-index} {ρ = ρ}
    {θ = θ} {θ′} {A} {A′} {p} {R} {left} {right}
    runtime simulation =
  forward-result-map
    {left-index = left-index}
    {source-result =
      OperationalValueResult ⟦ A ⟧[ θ ] ⟦ A′ ⟧[ θ′ ]}
    {target-result = FramedValueResult ρ θ θ′ p}
    {R = R} {left = left} {right = right}
    simulation
    (λ R≤S operational →
      framed-result
        (runtime-narrowing-weaken R≤S
          (left-world-typed (operational-typed operational))
          (right-world-typed (operational-typed operational))
          runtime)
        (operationally-framed-value operational))

operational-backward-to-framed :
  ∀ {W W′ Φ Δᴸ Δᴿ right-index}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {θ θ′ A A′}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {R : WorldRelation W W′}
    {left right} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  BackwardReturnSimulation
    (OperationalValueResult ⟦ A ⟧[ θ ] ⟦ A′ ⟧[ θ′ ])
    R left right right-index →
  BackwardReturnSimulation
    (FramedValueResult ρ θ θ′ p) R left right right-index
operational-backward-to-framed
    {right-index = right-index} {ρ = ρ}
    {θ = θ} {θ′} {A} {A′} {p} {R} {left} {right}
    runtime simulation =
  backward-result-map
    {right-index = right-index}
    {source-result =
      OperationalValueResult ⟦ A ⟧[ θ ] ⟦ A′ ⟧[ θ′ ]}
    {target-result = FramedValueResult ρ θ θ′ p}
    {R = R} {left = left} {right = right}
    simulation
    (λ R≤S operational →
      framed-result
        (runtime-narrowing-weaken R≤S
          (left-world-typed (operational-typed operational))
          (right-world-typed (operational-typed operational))
          runtime)
        (operationally-framed-value operational))

framed-term-forward-to-operational :
  ∀ {index Φ Δᴸ Δᴿ}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {γᵀ : NTI.CtxImp Φ Δᴸ Δᴿ}
    {N N′ : N.Term} {A A′ : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
  FramedDirectionalInterpreterTermSimulation
    forward-direction index Φ Δᴸ Δᴿ ρ γᵀ N N′ A A′ p →
  AssumptionMembershipUnique Φ →
  DirectionalInterpreterTermSimulation
    forward-direction index Φ Δᴸ Δᴿ ρ γᵀ N N′ A A′ p
framed-term-forward-to-operational
    {index} {Φ} {Δᴸ} {Δᴿ} {ρ} {γᵀ} {N} {N′} {A} {A′} {p}
    simulation unique {W} {W′} {θ} {θ′} {γ} {γ′} {R}
    runtime environment origins terms =
  framed-forward-to-operational
    {left-index = index} {ρ = ρ} {θ = θ} {θ′ = θ′}
    {A = A} {A′ = A′} {p = p} {R = R}
    {left = interpret W γ θ N} {right = interpret W′ γ′ θ′ N′}
    (simulation unique runtime environment
      (operational-environment-frame runtime origins) terms)

framed-term-backward-to-operational :
  ∀ {index Φ Δᴸ Δᴿ}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {γᵀ : NTI.CtxImp Φ Δᴸ Δᴿ}
    {N N′ : N.Term} {A A′ : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
  AssumptionMembershipUnique Φ →
  FramedDirectionalInterpreterTermSimulation
    backward-direction index Φ Δᴸ Δᴿ ρ γᵀ N N′ A A′ p →
  DirectionalInterpreterTermSimulation
    backward-direction index Φ Δᴸ Δᴿ ρ γᵀ N N′ A A′ p
framed-term-backward-to-operational
    {index} {Φ} {Δᴸ} {Δᴿ} {ρ} {γᵀ} {N} {N′} {A} {A′} {p}
    unique simulation {W} {W′} {θ} {θ′} {γ} {γ′} {R}
    runtime environment origins terms =
  framed-backward-to-operational
    {right-index = index} {ρ = ρ} {θ = θ} {θ′ = θ′}
    {A = A} {A′ = A′} {p = p} {R = R}
    {left = interpret W γ θ N} {right = interpret W′ γ′ θ′ N′}
    (simulation unique runtime environment
      (operational-environment-frame runtime origins) terms)

framed-term-target-blame-to-operational :
  ∀ {index Φ Δᴸ Δᴿ}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {γᵀ : NTI.CtxImp Φ Δᴸ Δᴿ}
    {N N′ : N.Term} {A A′ : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
  AssumptionMembershipUnique Φ →
  FramedDirectionalInterpreterTermSimulation
    target-blame-direction index
    Φ Δᴸ Δᴿ ρ γᵀ N N′ A A′ p →
  DirectionalInterpreterTermSimulation
    target-blame-direction index
    Φ Δᴸ Δᴿ ρ γᵀ N N′ A A′ p
framed-term-target-blame-to-operational
    {index} {Φ} {Δᴸ} {Δᴿ} {ρ} {γᵀ} {N} {N′} {A} {A′} {p}
    unique simulation {W} {W′} {θ} {θ′} {γ} {γ′} {R}
    runtime environment origins terms =
  simulation unique runtime environment
    (operational-environment-frame runtime origins) terms

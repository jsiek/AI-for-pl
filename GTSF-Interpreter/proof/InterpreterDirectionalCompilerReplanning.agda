module proof.InterpreterDirectionalCompilerReplanning where

-- File Charter:
--   * Transports exact application observations across compiler-selected
--     relational-store plans with identical executable endpoints.
--   * Preserves the inner producer certificate in every returned value.
--   * Contains no interpreter recursion, reduction, or catch-up theorem.

open import ImprecisionWf using (_∣_⊢_⊑_⊣_)

open import Interpreter
open import Simulation.Directional.InterpreterDirectionalSimulationMotive
open import Narrowing.InterpreterFramedValueNarrowing
open import Narrowing.InterpreterFramedValueNarrowingProperties
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Simulation.Core.InterpreterSimulationContext
open import Simulation.Core.InterpreterSimulationContextProperties using
  (runtime-narrowing-weaken)
open import Narrowing.InterpreterTermNarrowing
import NuTermImprecision as NTI
open import
  proof.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import proof.InterpreterDirectionalTransport using
  (backward-result-map; forward-result-map)
open import Types

open Narrowing.InterpreterTermNarrowing.RelatedWorlds


compiler-replanned-application-forward :
  ∀ {index W W′ Φ Δᴸ Δᴿ}
    {ρ ρ′ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {θ θ′ A A′ B B′ V V′ U U′}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′}
    {runtime′ : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ′ θ θ′} →
  FramedDirectionalApplyValueSimulation forward-direction index →
  AssumptionMembershipUnique Φ →
  FramedValueNarrowing
    {A = A ⇒ B} {A′ = A′ ⇒ B′}
    {p = pA ImprecisionWf.↦ pB} runtime V V′ →
  FramedValueNarrowing
    {A = A} {A′ = A′} {p = pA} runtime′ U U′ →
  ForwardReturnSimulation
    (FramedValueResult ρ′ θ θ′ pB) R
    (applyValue W V U) (applyValue W′ V′ U′) index
compiler-replanned-application-forward
    {index} {W} {W′} {ρ = ρ} {ρ′} {θ} {θ′}
    {V = V} {V′} {U} {U′} {pB = pB} {R = R}
    {runtime = runtime} {runtime′ = runtime′}
    application unique value argument =
  forward-result-map
    {left-index = index}
    {source-result = FramedValueResult ρ θ θ′ pB}
    {target-result = FramedValueResult ρ′ θ θ′ pB}
    {R = R}
    {left = applyValue W V U}
    {right = applyValue W′ V′ U′}
    (application unique runtime value argument′)
    (λ
      { R≤S (framed-result returned-runtime result) →
          framed-result
            (runtime-narrowing-weaken R≤S
              (left-world-typed returned-runtime)
              (right-world-typed returned-runtime)
              runtime′)
            (compiler-replanned-value
              (framed-value-typed result)
              (framed-value-operational result)
              result)
      })
  where
  argument′ =
    compiler-replanned-value
      (framed-value-typed argument)
      (framed-value-operational argument)
      argument


compiler-replanned-application-backward :
  ∀ {index W W′ Φ Δᴸ Δᴿ}
    {ρ ρ′ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {θ θ′ A A′ B B′ V V′ U U′}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′}
    {runtime′ : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ′ θ θ′} →
  FramedDirectionalApplyValueSimulation backward-direction index →
  AssumptionMembershipUnique Φ →
  FramedValueNarrowing
    {A = A ⇒ B} {A′ = A′ ⇒ B′}
    {p = pA ImprecisionWf.↦ pB} runtime V V′ →
  FramedValueNarrowing
    {A = A} {A′ = A′} {p = pA} runtime′ U U′ →
  BackwardReturnSimulation
    (FramedValueResult ρ′ θ θ′ pB) R
    (applyValue W V U) (applyValue W′ V′ U′) index
compiler-replanned-application-backward
    {index} {W} {W′} {ρ = ρ} {ρ′} {θ} {θ′}
    {V = V} {V′} {U} {U′} {pB = pB} {R = R}
    {runtime = runtime} {runtime′ = runtime′}
    application unique value argument =
  backward-result-map
    {right-index = index}
    {source-result = FramedValueResult ρ θ θ′ pB}
    {target-result = FramedValueResult ρ′ θ θ′ pB}
    {R = R}
    {left = applyValue W V U}
    {right = applyValue W′ V′ U′}
    (application unique runtime value argument′)
    (λ
      { R≤S (framed-result returned-runtime result) →
          framed-result
            (runtime-narrowing-weaken R≤S
              (left-world-typed returned-runtime)
              (right-world-typed returned-runtime)
              runtime′)
            (compiler-replanned-value
              (framed-value-typed result)
              (framed-value-operational result)
              result)
      })
  where
  argument′ =
    compiler-replanned-value
      (framed-value-typed argument)
      (framed-value-operational argument)
      argument


compiler-replanned-application-target-blame :
  ∀ {index W W′ Φ Δᴸ Δᴿ}
    {ρ ρ′ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {θ θ′ A A′ B B′ V V′ U U′}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′}
    {runtime′ : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ′ θ θ′} →
  FramedDirectionalApplyValueSimulation target-blame-direction index →
  AssumptionMembershipUnique Φ →
  FramedValueNarrowing
    {A = A ⇒ B} {A′ = A′ ⇒ B′}
    {p = pA ImprecisionWf.↦ pB} runtime V V′ →
  FramedValueNarrowing
    {A = A} {A′ = A′} {p = pA} runtime′ U U′ →
  TargetBlameSimulation R
    (applyValue W V U) (applyValue W′ V′ U′) index
compiler-replanned-application-target-blame
    {runtime = runtime}
    application unique value argument =
  application unique runtime value argument′
  where
  argument′ =
    compiler-replanned-value
      (framed-value-typed argument)
      (framed-value-operational argument)
      argument

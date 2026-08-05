module proof.InterpreterDirectionalFramedRightCastTerm where

-- File Charter:
--   * Dispatches both compiler-produced target-only cast roots after static
--     inversion through arbitrary allocation prefixes.
--   * Supplies the exact body and reachable coercion plan to the checked
--     directional right-cast composition theorem.
--   * Contains no recursion, reduction, catch-up, or DGG theorem.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Product using (_×_; _,_)
open import Data.Nat using (suc)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import Interpreter
open import Simulation.Directional.InterpreterDirectionalSimulationMotive
open import Narrowing.InterpreterFramedValueNarrowing
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Narrowing.InterpreterReachableCoercionNarrowing using
  (reachable-component)
open import Simulation.Core.InterpreterSimulationContext
open import Narrowing.InterpreterTermNarrowing
open import Narrowing.InterpreterTermNarrowingInversion
import NuTermImprecision as NTI
import NuTerms as N
open import proof.InterpreterDirectionalRightCast using
  ( directional-right-cast-backward
  ; directional-right-cast-forward
  ; directional-right-cast-target-blame
  )
open import
  proof.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import Types

open Narrowing.InterpreterTermNarrowing.RelatedWorlds


right-narrowing-cast-forward :
  ∀ {index W W′ Φ Δᴸ Δᴿ ρ γᵀ
      θ θ′ γ γ′ M M′ c′ A B′ q}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  AssumptionMembershipUnique Φ →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  FramedEnvironmentNarrowing runtime γᵀ γ γ′ →
  (terms :
    OpenInterpreterTermNarrowing
      R Φ Δᴸ Δᴿ ρ γᵀ M (M′ N.⟨ c′ ⟩) A B′ q) →
  aligned-term-root (term-alignment terms) ≡
    right-narrowing-cast-rootᴬ →
  (∀ {A′} {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
    FramedDirectionalInterpreterTermSimulation
      forward-direction (suc index)
      Φ Δᴸ Δᴿ ρ γᵀ M M′ A A′ p) →
  FramedDirectionalCoercionSimulation
    forward-direction (suc index) →
  ForwardReturnSimulation
    (FramedValueResult ρ θ θ′ q) R
    (interpret W γ θ M)
    (interpret W′ γ′ θ′ (M′ N.⟨ c′ ⟩))
    (suc index)
right-narrowing-cast-forward
    unique environment origins terms root term coercion
    with right-narrowing-cast-open-body terms root
right-narrowing-cast-forward
    unique environment origins terms root term coercion
    | A′ , p , body , action =
  directional-right-cast-forward
    unique environment origins body
    (reachable-component action)
    (term {A′ = A′} {p = p}) coercion


right-id-widening-cast-forward :
  ∀ {index W W′ Φ Δᴸ Δᴿ ρ γᵀ
      θ θ′ γ γ′ M M′ c′ A B′ q}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  AssumptionMembershipUnique Φ →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  FramedEnvironmentNarrowing runtime γᵀ γ γ′ →
  (terms :
    OpenInterpreterTermNarrowing
      R Φ Δᴸ Δᴿ ρ γᵀ M (M′ N.⟨ c′ ⟩) A B′ q) →
  aligned-term-root (term-alignment terms) ≡
    right-id-widening-cast-rootᴬ →
  (∀ {A′} {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
    FramedDirectionalInterpreterTermSimulation
      forward-direction (suc index)
      Φ Δᴸ Δᴿ ρ γᵀ M M′ A A′ p) →
  FramedDirectionalCoercionSimulation
    forward-direction (suc index) →
  ForwardReturnSimulation
    (FramedValueResult ρ θ θ′ q) R
    (interpret W γ θ M)
    (interpret W′ γ′ θ′ (M′ N.⟨ c′ ⟩))
    (suc index)
right-id-widening-cast-forward
    unique environment origins terms root term coercion
    with right-id-widening-cast-open-body terms root
right-id-widening-cast-forward
    unique environment origins terms root term coercion
    | A′ , p , body , action =
  directional-right-cast-forward
    unique environment origins body
    (reachable-component action)
    (term {A′ = A′} {p = p}) coercion


right-narrowing-cast-backward :
  ∀ {index W W′ Φ Δᴸ Δᴿ ρ γᵀ
      θ θ′ γ γ′ M M′ c′ A B′ q}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  AssumptionMembershipUnique Φ →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  FramedEnvironmentNarrowing runtime γᵀ γ γ′ →
  (terms :
    OpenInterpreterTermNarrowing
      R Φ Δᴸ Δᴿ ρ γᵀ M (M′ N.⟨ c′ ⟩) A B′ q) →
  aligned-term-root (term-alignment terms) ≡
    right-narrowing-cast-rootᴬ →
  (∀ {A′} {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
    FramedDirectionalInterpreterTermSimulation
      backward-direction index
      Φ Δᴸ Δᴿ ρ γᵀ M M′ A A′ p
    ×
    FramedDirectionalInterpreterTermSimulation
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
right-narrowing-cast-backward
    unique environment origins terms root term coercion
    with right-narrowing-cast-open-body terms root
right-narrowing-cast-backward
    unique environment origins terms root term coercion
    | A′ , p , body , action =
  directional-right-cast-backward
    unique environment origins body
    (reachable-component action)
    (term {A′ = A′} {p = p}) coercion


right-id-widening-cast-backward :
  ∀ {index W W′ Φ Δᴸ Δᴿ ρ γᵀ
      θ θ′ γ γ′ M M′ c′ A B′ q}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  AssumptionMembershipUnique Φ →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  FramedEnvironmentNarrowing runtime γᵀ γ γ′ →
  (terms :
    OpenInterpreterTermNarrowing
      R Φ Δᴸ Δᴿ ρ γᵀ M (M′ N.⟨ c′ ⟩) A B′ q) →
  aligned-term-root (term-alignment terms) ≡
    right-id-widening-cast-rootᴬ →
  (∀ {A′} {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
    FramedDirectionalInterpreterTermSimulation
      backward-direction index
      Φ Δᴸ Δᴿ ρ γᵀ M M′ A A′ p
    ×
    FramedDirectionalInterpreterTermSimulation
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
right-id-widening-cast-backward
    unique environment origins terms root term coercion
    with right-id-widening-cast-open-body terms root
right-id-widening-cast-backward
    unique environment origins terms root term coercion
    | A′ , p , body , action =
  directional-right-cast-backward
    unique environment origins body
    (reachable-component action)
    (term {A′ = A′} {p = p}) coercion


right-narrowing-cast-target-blame :
  ∀ {index W W′ Φ Δᴸ Δᴿ ρ γᵀ
      θ θ′ γ γ′ M M′ c′ A B′ q}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  AssumptionMembershipUnique Φ →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  FramedEnvironmentNarrowing runtime γᵀ γ γ′ →
  (terms :
    OpenInterpreterTermNarrowing
      R Φ Δᴸ Δᴿ ρ γᵀ M (M′ N.⟨ c′ ⟩) A B′ q) →
  aligned-term-root (term-alignment terms) ≡
    right-narrowing-cast-rootᴬ →
  (∀ {A′} {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
    FramedDirectionalInterpreterTermSimulation
      backward-direction index
      Φ Δᴸ Δᴿ ρ γᵀ M M′ A A′ p
    ×
    FramedDirectionalInterpreterTermSimulation
      target-blame-direction index
      Φ Δᴸ Δᴿ ρ γᵀ M M′ A A′ p) →
  (FramedDirectionalCoercionSimulation backward-direction index
   × FramedDirectionalCoercionSimulation
      target-blame-direction index) →
  TargetBlameSimulation R
    (interpret W γ θ M)
    (interpret W′ γ′ θ′ (M′ N.⟨ c′ ⟩))
    (suc index)
right-narrowing-cast-target-blame
    unique environment origins terms root term coercion
    with right-narrowing-cast-open-body terms root
right-narrowing-cast-target-blame
    unique environment origins terms root term coercion
    | A′ , p , body , action =
  directional-right-cast-target-blame
    unique environment origins body
    (reachable-component action)
    (term {A′ = A′} {p = p}) coercion


right-id-widening-cast-target-blame :
  ∀ {index W W′ Φ Δᴸ Δᴿ ρ γᵀ
      θ θ′ γ γ′ M M′ c′ A B′ q}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  AssumptionMembershipUnique Φ →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  FramedEnvironmentNarrowing runtime γᵀ γ γ′ →
  (terms :
    OpenInterpreterTermNarrowing
      R Φ Δᴸ Δᴿ ρ γᵀ M (M′ N.⟨ c′ ⟩) A B′ q) →
  aligned-term-root (term-alignment terms) ≡
    right-id-widening-cast-rootᴬ →
  (∀ {A′} {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
    FramedDirectionalInterpreterTermSimulation
      backward-direction index
      Φ Δᴸ Δᴿ ρ γᵀ M M′ A A′ p
    ×
    FramedDirectionalInterpreterTermSimulation
      target-blame-direction index
      Φ Δᴸ Δᴿ ρ γᵀ M M′ A A′ p) →
  (FramedDirectionalCoercionSimulation backward-direction index
   × FramedDirectionalCoercionSimulation
      target-blame-direction index) →
  TargetBlameSimulation R
    (interpret W γ θ M)
    (interpret W′ γ′ θ′ (M′ N.⟨ c′ ⟩))
    (suc index)
right-id-widening-cast-target-blame
    unique environment origins terms root term coercion
    with right-id-widening-cast-open-body terms root
right-id-widening-cast-target-blame
    unique environment origins terms root term coercion
    | A′ , p , body , action =
  directional-right-cast-target-blame
    unique environment origins body
    (reachable-component action)
    (term {A′ = A′} {p = p}) coercion

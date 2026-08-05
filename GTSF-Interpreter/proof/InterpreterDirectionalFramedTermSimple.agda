module proof.InterpreterDirectionalFramedTermSimple where

-- File Charter:
--   * Projects exact framed variable, closure, constant, and paired
--     type-abstraction simulations into the three fuel-local directions.
--   * Preserves producer origins needed by later application and
--     instantiation observers.
--   * Contains no interpreter recursion, reduction, or catch-up theorem.

open import Agda.Builtin.Equality using (_≡_)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)

open import Interpreter
open import Simulation.Directional.InterpreterDirectionalSimulationMotive
open import Simulation.Framed.InterpreterFramedTermSimple
open import Simulation.Framed.InterpreterFramedTypeAbstraction
open import Narrowing.InterpreterFramedValueNarrowing
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Simulation.Core.InterpreterSimulationContext
open import Narrowing.InterpreterTermNarrowing
import NuTermImprecision as NTI
import NuTerms as N
import Primitives
open import proof.InterpreterDirectionalSimulation using
  ( indexed-family-backward
  ; indexed-family-forward
  ; indexed-family-target-blame
  )
open import
  proof.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import Types

open Narrowing.InterpreterTermNarrowing.RelatedWorlds

directional-framed-variable-forward :
  ∀ {index W W′ Φ Δᴸ Δᴿ ρ γᵀ θ θ′ γ γ′ x A A′}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  FramedEnvironmentNarrowing runtime γᵀ γ γ′ →
  γᵀ ∋ x ⦂ NTI.ctx-imp A A′ p →
  ForwardReturnSimulation
    (FramedValueResult ρ θ θ′ p) R
    (interpret W γ θ (N.` x))
    (interpret W′ γ′ θ′ (N.` x)) index
directional-framed-variable-forward {index} origins lookup =
  indexed-family-forward {index = index}
    (λ left-index right-index →
      indexed-framed-variable
        {left-index = left-index} {right-index = right-index}
        origins lookup)

directional-framed-variable-backward :
  ∀ {index W W′ Φ Δᴸ Δᴿ ρ γᵀ θ θ′ γ γ′ x A A′}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  FramedEnvironmentNarrowing runtime γᵀ γ γ′ →
  γᵀ ∋ x ⦂ NTI.ctx-imp A A′ p →
  BackwardReturnSimulation
    (FramedValueResult ρ θ θ′ p) R
    (interpret W γ θ (N.` x))
    (interpret W′ γ′ θ′ (N.` x)) index
directional-framed-variable-backward {index} origins lookup =
  indexed-family-backward {index = index}
    (λ left-index right-index →
      indexed-framed-variable
        {left-index = left-index} {right-index = right-index}
        origins lookup)

directional-framed-variable-target-blame :
  ∀ {index W W′ Φ Δᴸ Δᴿ ρ γᵀ θ θ′ γ γ′ x A A′}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  FramedEnvironmentNarrowing runtime γᵀ γ γ′ →
  γᵀ ∋ x ⦂ NTI.ctx-imp A A′ p →
  TargetBlameSimulation R
    (interpret W γ θ (N.` x))
    (interpret W′ γ′ θ′ (N.` x)) index
directional-framed-variable-target-blame {index} origins lookup =
  indexed-family-target-blame {index = index}
    (λ left-index right-index →
      indexed-framed-variable
        {left-index = left-index} {right-index = right-index}
        origins lookup)

directional-framed-closure-forward :
  ∀ {index W W′ Φ Δᴸ Δᴿ ρ γᵀ
      θ θ′ γ γ′ N N′ A A′ B B′ pA pB}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  FramedEnvironmentNarrowing runtime γᵀ γ γ′ →
  AssumptionMembershipUnique Φ →
  (alignment :
    AlignedInterpreterTermNarrowing
      Φ Δᴸ Δᴿ ρ γᵀ
      (N.ƛ N) (N.ƛ N′)
      (A ⇒ B) (A′ ⇒ B′) (pA ImprecisionWf.↦ pB)) →
  ForwardReturnSimulation
    (FramedValueResult ρ θ θ′ (pA ImprecisionWf.↦ pB)) R
    (interpret W γ θ (N.ƛ N))
    (interpret W′ γ′ θ′ (N.ƛ N′)) index
directional-framed-closure-forward
    {index} environment origins unique alignment =
  indexed-family-forward {index = index}
    (λ left-index right-index →
      indexed-framed-closure
        {left-index = left-index} {right-index = right-index}
        environment origins unique alignment)

directional-framed-closure-backward :
  ∀ {index W W′ Φ Δᴸ Δᴿ ρ γᵀ
      θ θ′ γ γ′ N N′ A A′ B B′ pA pB}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  FramedEnvironmentNarrowing runtime γᵀ γ γ′ →
  AssumptionMembershipUnique Φ →
  (alignment :
    AlignedInterpreterTermNarrowing
      Φ Δᴸ Δᴿ ρ γᵀ
      (N.ƛ N) (N.ƛ N′)
      (A ⇒ B) (A′ ⇒ B′) (pA ImprecisionWf.↦ pB)) →
  BackwardReturnSimulation
    (FramedValueResult ρ θ θ′ (pA ImprecisionWf.↦ pB)) R
    (interpret W γ θ (N.ƛ N))
    (interpret W′ γ′ θ′ (N.ƛ N′)) index
directional-framed-closure-backward
    {index} environment origins unique alignment =
  indexed-family-backward {index = index}
    (λ left-index right-index →
      indexed-framed-closure
        {left-index = left-index} {right-index = right-index}
        environment origins unique alignment)

directional-framed-closure-target-blame :
  ∀ {index W W′ Φ Δᴸ Δᴿ ρ γᵀ
      θ θ′ γ γ′ N N′ A A′ B B′ pA pB}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  FramedEnvironmentNarrowing runtime γᵀ γ γ′ →
  AssumptionMembershipUnique Φ →
  (alignment :
    AlignedInterpreterTermNarrowing
      Φ Δᴸ Δᴿ ρ γᵀ
      (N.ƛ N) (N.ƛ N′)
      (A ⇒ B) (A′ ⇒ B′) (pA ImprecisionWf.↦ pB)) →
  TargetBlameSimulation R
    (interpret W γ θ (N.ƛ N))
    (interpret W′ γ′ θ′ (N.ƛ N′)) index
directional-framed-closure-target-blame
    {index} environment origins unique alignment =
  indexed-family-target-blame {index = index}
    (λ left-index right-index →
      indexed-framed-closure
        {left-index = left-index} {right-index = right-index}
        environment origins unique alignment)

directional-framed-constant-forward :
  ∀ {index W W′ Φ Δᴸ Δᴿ ρ γᵀ θ θ′ γ γ′ n}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  FramedEnvironmentNarrowing runtime γᵀ γ γ′ →
  ForwardReturnSimulation
    (FramedValueResult ρ θ θ′ ImprecisionWf.idι) R
    (interpret W γ θ (N.$ (Primitives.κℕ n)))
    (interpret W′ γ′ θ′ (N.$ (Primitives.κℕ n))) index
directional-framed-constant-forward
    {index} environment origins =
  indexed-family-forward {index = index}
    (λ left-index right-index →
      indexed-framed-constant
        {left-index = left-index} {right-index = right-index}
        environment origins)

directional-framed-constant-backward :
  ∀ {index W W′ Φ Δᴸ Δᴿ ρ γᵀ θ θ′ γ γ′ n}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  FramedEnvironmentNarrowing runtime γᵀ γ γ′ →
  BackwardReturnSimulation
    (FramedValueResult ρ θ θ′ ImprecisionWf.idι) R
    (interpret W γ θ (N.$ (Primitives.κℕ n)))
    (interpret W′ γ′ θ′ (N.$ (Primitives.κℕ n))) index
directional-framed-constant-backward
    {index} environment origins =
  indexed-family-backward {index = index}
    (λ left-index right-index →
      indexed-framed-constant
        {left-index = left-index} {right-index = right-index}
        environment origins)

directional-framed-constant-target-blame :
  ∀ {index W W′ Φ Δᴸ Δᴿ ρ γᵀ θ θ′ γ γ′ n}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  FramedEnvironmentNarrowing runtime γᵀ γ γ′ →
  TargetBlameSimulation R
    (interpret W γ θ (N.$ (Primitives.κℕ n)))
    (interpret W′ γ′ θ′ (N.$ (Primitives.κℕ n))) index
directional-framed-constant-target-blame
    {index} environment origins =
  indexed-family-target-blame {index = index}
    (λ left-index right-index →
      indexed-framed-constant
        {left-index = left-index} {right-index = right-index}
        environment origins)

directional-framed-paired-type-abstraction-forward :
  ∀ {index W W′ Φ Δᴸ Δᴿ ρ γᵀ
      θ θ′ γ γ′ V V′ A B p}
    {R : WorldRelation W W′} →
  AssumptionMembershipUnique Φ →
  (alignment :
    AlignedInterpreterTermNarrowing
      Φ Δᴸ Δᴿ ρ γᵀ
      (N.Λ V) (N.Λ V′) (`∀ A) (`∀ B) p) →
  aligned-term-root alignment ≡ paired-type-abstraction-rootᴬ →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  FramedEnvironmentNarrowing runtime γᵀ γ γ′ →
  ForwardReturnSimulation
    (FramedValueResult ρ θ θ′ p) R
    (interpret W γ θ (N.Λ V))
    (interpret W′ γ′ θ′ (N.Λ V′)) index
directional-framed-paired-type-abstraction-forward
    {index} unique alignment root runtime environment origins =
  indexed-family-forward {index = index}
    (λ left-index right-index →
      indexed-framed-paired-type-abstraction
        {left-index = left-index} {right-index = right-index}
        unique alignment root runtime environment origins)

directional-framed-paired-type-abstraction-backward :
  ∀ {index W W′ Φ Δᴸ Δᴿ ρ γᵀ
      θ θ′ γ γ′ V V′ A B p}
    {R : WorldRelation W W′} →
  AssumptionMembershipUnique Φ →
  (alignment :
    AlignedInterpreterTermNarrowing
      Φ Δᴸ Δᴿ ρ γᵀ
      (N.Λ V) (N.Λ V′) (`∀ A) (`∀ B) p) →
  aligned-term-root alignment ≡ paired-type-abstraction-rootᴬ →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  FramedEnvironmentNarrowing runtime γᵀ γ γ′ →
  BackwardReturnSimulation
    (FramedValueResult ρ θ θ′ p) R
    (interpret W γ θ (N.Λ V))
    (interpret W′ γ′ θ′ (N.Λ V′)) index
directional-framed-paired-type-abstraction-backward
    {index} unique alignment root runtime environment origins =
  indexed-family-backward {index = index}
    (λ left-index right-index →
      indexed-framed-paired-type-abstraction
        {left-index = left-index} {right-index = right-index}
        unique alignment root runtime environment origins)

directional-framed-paired-type-abstraction-target-blame :
  ∀ {index W W′ Φ Δᴸ Δᴿ ρ γᵀ
      θ θ′ γ γ′ V V′ A B p}
    {R : WorldRelation W W′} →
  AssumptionMembershipUnique Φ →
  (alignment :
    AlignedInterpreterTermNarrowing
      Φ Δᴸ Δᴿ ρ γᵀ
      (N.Λ V) (N.Λ V′) (`∀ A) (`∀ B) p) →
  aligned-term-root alignment ≡ paired-type-abstraction-rootᴬ →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  FramedEnvironmentNarrowing runtime γᵀ γ γ′ →
  TargetBlameSimulation R
    (interpret W γ θ (N.Λ V))
    (interpret W′ γ′ θ′ (N.Λ V′)) index
directional-framed-paired-type-abstraction-target-blame
    {index} unique alignment root runtime environment origins =
  indexed-family-target-blame {index = index}
    (λ left-index right-index →
      indexed-framed-paired-type-abstraction
        {left-index = left-index} {right-index = right-index}
        unique alignment root runtime environment origins)

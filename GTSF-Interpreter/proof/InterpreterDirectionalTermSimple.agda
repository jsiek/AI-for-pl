module proof.InterpreterDirectionalTermSimple where

-- File Charter:
--   * Projects the variable, closure, constant, and paired type-abstraction
--     leaves into each direction of the fuel-local simulation.
--   * Reuses their exact indexed interpreter equations at arbitrary indices.
--   * Contains no interpreter recursion, reduction, or catch-up theorem.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Nat using (zero)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)

open import Interpreter
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Simulation.Indexed.InterpreterIndexedTermSimple
open import Simulation.Indexed.InterpreterIndexedTypeAbstraction
open import Narrowing.InterpreterOperationalValueNarrowing
open import Typing.InterpreterSemanticTypingCore using
  (WorldTyping; base-type; _⇒ᵛ_; ⟦_⟧[_])
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
open import Types

open Narrowing.InterpreterTermNarrowing.RelatedWorlds

directional-variable-forward :
  ∀ {index W W′ Φ Δᴸ Δᴿ ρ γᵀ θ θ′ γ γ′ x A A′}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  OperationalEnvironmentNarrowing θ θ′ R γᵀ γ γ′ →
  γᵀ ∋ x ⦂ NTI.ctx-imp A A′ p →
  ForwardReturnSimulation
    (OperationalValueResult ⟦ A ⟧[ θ ] ⟦ A′ ⟧[ θ′ ]) R
    (interpret W γ θ (N.` x))
    (interpret W′ γ′ θ′ (N.` x)) index
directional-variable-forward {index} environment origins lookup =
  indexed-family-forward {index = index}
    (λ left-index right-index →
      indexed-variable-simulation
        {left-index = left-index} {right-index = right-index}
        environment origins lookup)

directional-variable-backward :
  ∀ {index W W′ Φ Δᴸ Δᴿ ρ γᵀ θ θ′ γ γ′ x A A′}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  OperationalEnvironmentNarrowing θ θ′ R γᵀ γ γ′ →
  γᵀ ∋ x ⦂ NTI.ctx-imp A A′ p →
  BackwardReturnSimulation
    (OperationalValueResult ⟦ A ⟧[ θ ] ⟦ A′ ⟧[ θ′ ]) R
    (interpret W γ θ (N.` x))
    (interpret W′ γ′ θ′ (N.` x)) index
directional-variable-backward {index} environment origins lookup =
  indexed-family-backward {index = index}
    (λ left-index right-index →
      indexed-variable-simulation
        {left-index = left-index} {right-index = right-index}
        environment origins lookup)

directional-variable-target-blame :
  ∀ {index W W′ Φ Δᴸ Δᴿ ρ γᵀ θ θ′ γ γ′ x A A′}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  OperationalEnvironmentNarrowing θ θ′ R γᵀ γ γ′ →
  γᵀ ∋ x ⦂ NTI.ctx-imp A A′ p →
  TargetBlameSimulation R
    (interpret W γ θ (N.` x))
    (interpret W′ γ′ θ′ (N.` x)) index
directional-variable-target-blame {index} environment origins lookup =
  indexed-family-target-blame {index = index}
    (λ left-index right-index →
      indexed-variable-simulation
        {left-index = left-index} {right-index = right-index}
        environment origins lookup)

directional-closure-forward :
  ∀ {index W W′ Φ Δᴸ Δᴿ ρ γᵀ θ θ′ γ γ′
      N N′ A A′ B B′ pA pB}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  OperationalEnvironmentNarrowing θ θ′ R γᵀ γ γ′ →
  (terms :
    OpenInterpreterTermNarrowing R Φ Δᴸ Δᴿ ρ γᵀ
      (N.ƛ N) (N.ƛ N′)
      (A ⇒ B) (A′ ⇒ B′) (pA ImprecisionWf.↦ pB)) →
  ForwardReturnSimulation
    (OperationalValueResult
      (⟦ A ⟧[ θ ] ⇒ᵛ ⟦ B ⟧[ θ ])
      (⟦ A′ ⟧[ θ′ ] ⇒ᵛ ⟦ B′ ⟧[ θ′ ]))
    R (interpret W γ θ (N.ƛ N))
    (interpret W′ γ′ θ′ (N.ƛ N′)) index
directional-closure-forward {index} environment origins terms =
  indexed-family-forward {index = index}
    (λ left-index right-index →
      indexed-closure-simulation
        {left-index = left-index} {right-index = right-index}
        environment origins terms)

directional-closure-backward :
  ∀ {index W W′ Φ Δᴸ Δᴿ ρ γᵀ θ θ′ γ γ′
      N N′ A A′ B B′ pA pB}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  OperationalEnvironmentNarrowing θ θ′ R γᵀ γ γ′ →
  (terms :
    OpenInterpreterTermNarrowing R Φ Δᴸ Δᴿ ρ γᵀ
      (N.ƛ N) (N.ƛ N′)
      (A ⇒ B) (A′ ⇒ B′) (pA ImprecisionWf.↦ pB)) →
  BackwardReturnSimulation
    (OperationalValueResult
      (⟦ A ⟧[ θ ] ⇒ᵛ ⟦ B ⟧[ θ ])
      (⟦ A′ ⟧[ θ′ ] ⇒ᵛ ⟦ B′ ⟧[ θ′ ]))
    R (interpret W γ θ (N.ƛ N))
    (interpret W′ γ′ θ′ (N.ƛ N′)) index
directional-closure-backward {index} environment origins terms =
  indexed-family-backward {index = index}
    (λ left-index right-index →
      indexed-closure-simulation
        {left-index = left-index} {right-index = right-index}
        environment origins terms)

directional-closure-target-blame :
  ∀ {index W W′ Φ Δᴸ Δᴿ ρ γᵀ θ θ′ γ γ′
      N N′ A A′ B B′ pA pB}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  OperationalEnvironmentNarrowing θ θ′ R γᵀ γ γ′ →
  (terms :
    OpenInterpreterTermNarrowing R Φ Δᴸ Δᴿ ρ γᵀ
      (N.ƛ N) (N.ƛ N′)
      (A ⇒ B) (A′ ⇒ B′) (pA ImprecisionWf.↦ pB)) →
  TargetBlameSimulation R
    (interpret W γ θ (N.ƛ N))
    (interpret W′ γ′ θ′ (N.ƛ N′)) index
directional-closure-target-blame {index} environment origins terms =
  indexed-family-target-blame {index = index}
    (λ left-index right-index →
      indexed-closure-simulation
        {left-index = left-index} {right-index = right-index}
        environment origins terms)

directional-constant-forward :
  ∀ {index W W′ γ γ′ θ θ′ n}
    {R : WorldRelation W W′} →
  WorldTyping W →
  WorldTyping W′ →
  ForwardReturnSimulation
    (OperationalValueResult (base-type `ℕ) (base-type `ℕ)) R
    (interpret W γ θ (N.$ (Primitives.κℕ n)))
    (interpret W′ γ′ θ′ (N.$ (Primitives.κℕ n))) index
directional-constant-forward
    {index} {γ = γ} {γ′} {θ} {θ′} W⊢ W′⊢ =
  indexed-family-forward {index = index}
    (λ _ _ →
      indexed-constant-simulation
        {γ = γ} {γ′ = γ′} {θ = θ} {θ′ = θ′}
        W⊢ W′⊢)

directional-constant-backward :
  ∀ {index W W′ γ γ′ θ θ′ n}
    {R : WorldRelation W W′} →
  WorldTyping W →
  WorldTyping W′ →
  BackwardReturnSimulation
    (OperationalValueResult (base-type `ℕ) (base-type `ℕ)) R
    (interpret W γ θ (N.$ (Primitives.κℕ n)))
    (interpret W′ γ′ θ′ (N.$ (Primitives.κℕ n))) index
directional-constant-backward
    {index} {γ = γ} {γ′} {θ} {θ′} W⊢ W′⊢ =
  indexed-family-backward {index = index}
    (λ _ _ →
      indexed-constant-simulation
        {γ = γ} {γ′ = γ′} {θ = θ} {θ′ = θ′}
        W⊢ W′⊢)

directional-constant-target-blame :
  ∀ {index W W′ γ γ′ θ θ′ n}
    {R : WorldRelation W W′} →
  WorldTyping W →
  WorldTyping W′ →
  TargetBlameSimulation R
    (interpret W γ θ (N.$ (Primitives.κℕ n)))
    (interpret W′ γ′ θ′ (N.$ (Primitives.κℕ n))) index
directional-constant-target-blame
    {index} {W} {W′} {γ} {γ′} {θ} {θ′} {n} {R} W⊢ W′⊢ =
  target-blame-reflects
    (indexed-constant-simulation
      {left-index = zero} {right-index = index}
      {W = W} {W′ = W′} {γ = γ} {γ′ = γ′}
      {θ = θ} {θ′ = θ′} {n = n} {R = R} W⊢ W′⊢)

directional-paired-type-abstraction-forward :
  ∀ {index W W′ Φ Δᴸ Δᴿ ρ γᵀ θ θ′ γ γ′ V V′ A B p}
    {R : WorldRelation W W′} →
  (alignment :
    AlignedInterpreterTermNarrowing
      Φ Δᴸ Δᴿ ρ γᵀ
      (N.Λ V) (N.Λ V′) (`∀ A) (`∀ B) p) →
  aligned-term-root alignment ≡ paired-type-abstraction-rootᴬ →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  OperationalEnvironmentNarrowing θ θ′ R γᵀ γ γ′ →
  ForwardReturnSimulation
    (OperationalValueResult ⟦ `∀ A ⟧[ θ ] ⟦ `∀ B ⟧[ θ′ ]) R
    (interpret W γ θ (N.Λ V))
    (interpret W′ γ′ θ′ (N.Λ V′)) index
directional-paired-type-abstraction-forward
    {index} alignment root runtime environment origins =
  indexed-family-forward {index = index}
    (λ left-index right-index →
      indexed-paired-type-abstraction-simulation
        {left-index = left-index} {right-index = right-index}
        alignment root runtime environment origins)

directional-paired-type-abstraction-backward :
  ∀ {index W W′ Φ Δᴸ Δᴿ ρ γᵀ θ θ′ γ γ′ V V′ A B p}
    {R : WorldRelation W W′} →
  (alignment :
    AlignedInterpreterTermNarrowing
      Φ Δᴸ Δᴿ ρ γᵀ
      (N.Λ V) (N.Λ V′) (`∀ A) (`∀ B) p) →
  aligned-term-root alignment ≡ paired-type-abstraction-rootᴬ →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  OperationalEnvironmentNarrowing θ θ′ R γᵀ γ γ′ →
  BackwardReturnSimulation
    (OperationalValueResult ⟦ `∀ A ⟧[ θ ] ⟦ `∀ B ⟧[ θ′ ]) R
    (interpret W γ θ (N.Λ V))
    (interpret W′ γ′ θ′ (N.Λ V′)) index
directional-paired-type-abstraction-backward
    {index} alignment root runtime environment origins =
  indexed-family-backward {index = index}
    (λ left-index right-index →
      indexed-paired-type-abstraction-simulation
        {left-index = left-index} {right-index = right-index}
        alignment root runtime environment origins)

directional-paired-type-abstraction-target-blame :
  ∀ {index W W′ Φ Δᴸ Δᴿ ρ γᵀ θ θ′ γ γ′ V V′ A B p}
    {R : WorldRelation W W′} →
  (alignment :
    AlignedInterpreterTermNarrowing
      Φ Δᴸ Δᴿ ρ γᵀ
      (N.Λ V) (N.Λ V′) (`∀ A) (`∀ B) p) →
  aligned-term-root alignment ≡ paired-type-abstraction-rootᴬ →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  OperationalEnvironmentNarrowing θ θ′ R γᵀ γ γ′ →
  TargetBlameSimulation R
    (interpret W γ θ (N.Λ V))
    (interpret W′ γ′ θ′ (N.Λ V′)) index
directional-paired-type-abstraction-target-blame
    {index} alignment root runtime environment origins =
  indexed-family-target-blame {index = index}
    (λ left-index right-index →
      indexed-paired-type-abstraction-simulation
        {left-index = left-index} {right-index = right-index}
        alignment root runtime environment origins)

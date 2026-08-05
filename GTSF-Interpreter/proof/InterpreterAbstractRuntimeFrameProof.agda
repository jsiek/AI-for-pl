module proof.InterpreterAbstractRuntimeFrameProof where

-- File Charter:
--   * Constructs the source-only runtime below an abstract type binder.
--   * Shifts the static store, runtime contexts, and realization evidence.
--   * Lifts typed synchronized term environments into the abstract runtime.
--   * Contains no interpreter call, allocation, reduction, or catch-up result.

open import Data.List using (_∷_)
open import Data.Nat using (suc; zero)
open import Data.Nat.Properties using (m≤n⊔m; ≤-trans)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import ImprecisionWf using (_ˣ⊑★; ⇑ᴸᵢ)
open import Interpreter
open import Typing.InterpreterSemanticTypingCore using (RuntimeContext)
open import Simulation.Core.InterpreterSimulationContext
open import Narrowing.InterpreterTermNarrowing
open import Runtime.InterpreterTypeEnvironmentClosing using
  (left-abstract-realization)
open import Narrowing.InterpreterWorldNarrowing using (abstract-scoped)
import NuTermImprecision as NTI
open import proof.InterpreterInstantiationStore using
  (left-lift-store-correspondence-realization)
open import
  proof.NuImprecisionAssumptionMembershipUniquenessProof using
  (assumption-membership-unique-source)
import proof.InterpreterSemanticTypingProperties as SemanticProof

open Narrowing.InterpreterTermNarrowing.RelatedWorlds

left-abstract-runtime :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ ρ↑ θ θ′ X}
    {R : WorldRelation W W′} →
  RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′ →
  NTI.LiftLeftStoreⁱ
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ↑ →
  RuntimeNarrowing R
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
    (suc Δᴸ) Δᴿ ρ↑
    (abstract-name X ∷ θ) θ′
left-abstract-runtime
    {Δᴸ = Δᴸ} {Δᴿ} {ρ↑ = ρ↑} {θ} {θ′}
    {X = type-name X}
    runtime liftρ =
  runtime-narrowing
    (assumption-membership-unique-source
      (assumption-membership-unique runtime))
    (left-world-typed runtime)
    (right-world-typed runtime)
    left-context
    right-context
    (right-runtime-environment runtime)
    (left-lift-store-correspondence-realization
      liftρ (store-correspondences-realized runtime))
    (left-abstract-realization
      (type-environments-realized runtime))
    (≤-trans (abstract-supply runtime)
      (m≤n⊔m (suc X) (nextAbstractIndex θ)))
  where
  left-context :
    RuntimeContext _ (suc Δᴸ) (NTI.leftStoreⁱ ρ↑)
      (abstract-name (type-name X) ∷ θ)
  left-context =
    subst
      (λ Σ →
        RuntimeContext _ (suc Δᴸ) Σ
          (abstract-name (type-name X) ∷ θ))
      (sym (NTI.leftStoreⁱ-lift-left liftρ))
      (SemanticProof.runtime-context-name
        abstract-scoped
        (left-runtime-context runtime))

  right-context :
    RuntimeContext _ Δᴿ (NTI.rightStoreⁱ ρ↑) θ′
  right-context =
    subst
      (λ Σ → RuntimeContext _ Δᴿ Σ θ′)
      (sym (NTI.rightStoreⁱ-lift-left liftρ))
      (right-runtime-context runtime)

left-abstract-environment-realization :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ ρ↑ θ θ′ γᵀ γᵀ↑ γ γ′ X}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′}
    {runtime↑ :
      RuntimeNarrowing R
        ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        (suc Δᴸ) Δᴿ ρ↑
        (abstract-name X ∷ θ) θ′} →
  NTI.LiftLeftCtxⁱ
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) γᵀ γᵀ↑ →
  EnvironmentRealization runtime γᵀ γ γ′ →
  EnvironmentRealization runtime↑ γᵀ↑ γ γ′
left-abstract-environment-realization
    {W = W} {W′} {θ = θ} {θ′} {γ = γ} {γ′}
    {X = X} {runtime↑ = runtime↑}
    liftγ environment =
  environment-realization
    (environments-narrow environment)
    (subst
      (Typing.InterpreterSemanticTypingCore.EnvironmentTyping
        W (abstract-name X ∷ θ) γ)
      (sym (NTI.leftCtxⁱ-lift-left liftγ))
      (SemanticProof.environment-type-weaken
        (abstract-name X)
        (left-environment-typed environment)))
    (subst
      (Typing.InterpreterSemanticTypingCore.EnvironmentTyping W′ θ′ γ′)
      (sym (NTI.rightCtxⁱ-lift-left liftγ))
      (right-environment-typed environment))

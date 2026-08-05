module proof.InterpreterFramedEnvironmentLiftProof where

-- File Charter:
--   * Reindexes exact runtime values when a polymorphic allocation shifts
--     the static term context.
--   * Uses precision-index uniqueness only to identify the compiler's
--     proof-relevant lifted entries with their canonical renamings.
--   * Contains no interpreter call, reduction, or catch-up result.

open import Data.List using (_∷_)
open import Data.Nat using (suc; zero)
open import Relation.Binary.PropositionalEquality using (refl; subst; sym)

open import ImprecisionWf using
  (_ˣ⊑★; _ˣ⊑ˣ_; ⇑ᵢ; ⇑ᴸᵢ)
open import Interpreter
open import Narrowing.InterpreterFramedValueNarrowing
open import Narrowing.InterpreterFramedValueNarrowingProperties
open import Narrowing.InterpreterOperationalValueNarrowingProperties using
  (operational-value-narrowing-weaken)
open import Typing.InterpreterSemanticTypingCore
open import Simulation.Core.InterpreterSimulationContext
open import Narrowing.InterpreterTermNarrowing
open import Narrowing.InterpreterTypedValueNarrowing
open import Narrowing.InterpreterTypedValueNarrowingProperties
import NuTermImprecision as NTI
open import proof.InterpreterSemanticTypingProperties using
  (interpret-weaken)
open import proof.InterpreterOperationalEnvironmentLift using
  (operational-value-type-transport)
open import
  proof.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import
  proof.NuImprecisionAssumptionMembershipUniquenessLemma using
  (assumption-membership-unique→precision-index-unique)
open import
  proof.NuImprecisionAssumptionMembershipUniquenessProof using
  ( assumption-membership-unique-matched
  ; assumption-membership-unique-source
  )
open import proof.MaximalLowerBoundsWf using
  (∀ᵢᶜ; ⊑-lift∀ᵢ; ⊑-source-liftνᵢ)
open import Types

open Narrowing.InterpreterTermNarrowing.RelatedWorlds

paired-framed-environment-lift :
  ∀ {W W′ U U′ Φ Δᴸ Δᴿ ρ ρ↑ θ θ′ γᵀ γᵀ↑}
    {γ γ′ α α′}
    {R : WorldRelation W W′}
    {S : WorldRelation U U′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′}
    {runtime↑ :
      RuntimeNarrowing S (∀ᵢᶜ Φ)
        (suc Δᴸ) (suc Δᴿ) ρ↑
        (seal-name α ∷ θ) (seal-name α′ ∷ θ′)} →
  AssumptionMembershipUnique Φ →
  RelatedWorlds.WorldExtension R S →
  NTI.LiftCtxⁱ (∀ᵢᶜ Φ) γᵀ γᵀ↑ →
  FramedEnvironmentNarrowing runtime γᵀ γ γ′ →
  FramedEnvironmentNarrowing runtime↑ γᵀ↑ γ γ′
paired-framed-environment-lift unique R≤S
    NTI.lift-ctx-[] []⊑[]ᶠ =
  []⊑[]ᶠ
paired-framed-environment-lift
    {θ = θ} {θ′} {α = α} {α′}
    {runtime↑ = runtime↑}
    unique R≤S
    (NTI.lift-ctx-∷ {A = A} {B = B}
      {p = p} {p′ = p↑} liftγ)
    (value ∷⊑∷ᶠ environment)
    with assumption-membership-unique→precision-index-unique
      (assumption-membership-unique-matched unique)
      p↑ (⊑-lift∀ᵢ p)
paired-framed-environment-lift
    {θ = θ} {θ′} {α = α} {α′}
    {runtime↑ = runtime↑}
    unique R≤S
    (NTI.lift-ctx-∷ {A = A} {B = B}
      {p = p} {p′ = p↑} liftγ)
    (value ∷⊑∷ᶠ environment)
    | refl =
  paired-lifted-value unique refl refl R≤S
    lifted-typed lifted-operational value
    ∷⊑∷ᶠ
  paired-framed-environment-lift unique R≤S liftγ environment
  where
  weakened =
    typed-value-narrowing-weaken R≤S
      (left-world-typed runtime↑)
      (right-world-typed runtime↑)
      (framed-value-typed value)

  lifted-typed =
    typed-value-type-transport
      (sym (interpret-weaken
        (nominal-type (seal-name α))
        (semanticEnvironment θ) A))
      (sym (interpret-weaken
        (nominal-type (seal-name α′))
        (semanticEnvironment θ′) B))
      weakened

  weakened-operational =
    operational-value-narrowing-weaken R≤S
      (left-world-typed runtime↑)
      (right-world-typed runtime↑)
      (framed-value-operational value)

  lifted-operational =
    operational-value-type-transport
      (sym (interpret-weaken
        (nominal-type (seal-name α))
        (semanticEnvironment θ) A))
      (sym (interpret-weaken
        (nominal-type (seal-name α′))
        (semanticEnvironment θ′) B))
      weakened-operational

left-framed-environment-lift :
  ∀ {W W′ U U′ Φ Δᴸ Δᴿ ρ ρ↑ θ θ′ γᵀ γᵀ↑}
    {γ γ′ α}
    {R : WorldRelation W W′}
    {S : WorldRelation U U′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′}
    {runtime↑ :
      RuntimeNarrowing S
        ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        (suc Δᴸ) Δᴿ ρ↑
        (seal-name α ∷ θ) θ′} →
  AssumptionMembershipUnique Φ →
  RelatedWorlds.WorldExtension R S →
  NTI.LiftLeftCtxⁱ
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) γᵀ γᵀ↑ →
  FramedEnvironmentNarrowing runtime γᵀ γ γ′ →
  FramedEnvironmentNarrowing runtime↑ γᵀ↑ γ γ′
left-framed-environment-lift unique R≤S
    NTI.lift-left-ctx-[] []⊑[]ᶠ =
  []⊑[]ᶠ
left-framed-environment-lift
    {θ = θ} {α = α}
    {runtime↑ = runtime↑}
    unique R≤S
    (NTI.lift-left-ctx-∷ {A = A} {B = B}
      {p = p} {p′ = p↑} liftγ)
    (value ∷⊑∷ᶠ environment)
    with assumption-membership-unique→precision-index-unique
      (assumption-membership-unique-source unique)
      p↑ (⊑-source-liftνᵢ p)
left-framed-environment-lift
    {θ = θ} {α = α}
    {runtime↑ = runtime↑}
    unique R≤S
    (NTI.lift-left-ctx-∷ {A = A} {B = B}
      {p = p} {p′ = p↑} liftγ)
    (value ∷⊑∷ᶠ environment)
    | refl =
  left-lifted-value unique refl R≤S
    lifted-typed lifted-operational value
    ∷⊑∷ᶠ
  left-framed-environment-lift unique R≤S liftγ environment
  where
  weakened =
    typed-value-narrowing-weaken R≤S
      (left-world-typed runtime↑)
      (right-world-typed runtime↑)
      (framed-value-typed value)

  lifted-typed =
    typed-value-type-transport
      (sym (interpret-weaken
        (nominal-type (seal-name α))
        (semanticEnvironment θ) A))
      refl
      weakened

  weakened-operational =
    operational-value-narrowing-weaken R≤S
      (left-world-typed runtime↑)
      (right-world-typed runtime↑)
      (framed-value-operational value)

  lifted-operational =
    operational-value-type-transport
      (sym (interpret-weaken
        (nominal-type (seal-name α))
        (semanticEnvironment θ) A))
      refl
      weakened-operational

left-abstract-framed-environment-lift :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ ρ↑ θ θ′ γᵀ γᵀ↑ γ γ′ X}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′}
    {runtime↑ :
      RuntimeNarrowing R
        ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        (suc Δᴸ) Δᴿ ρ↑
        (abstract-name X ∷ θ) θ′} →
  AssumptionMembershipUnique Φ →
  NTI.LiftLeftCtxⁱ
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) γᵀ γᵀ↑ →
  FramedEnvironmentNarrowing runtime γᵀ γ γ′ →
  FramedEnvironmentNarrowing runtime↑ γᵀ↑ γ γ′
left-abstract-framed-environment-lift unique
    NTI.lift-left-ctx-[] []⊑[]ᶠ =
  []⊑[]ᶠ
left-abstract-framed-environment-lift
    {θ = θ} {X = X} {runtime↑ = runtime↑}
    unique
    (NTI.lift-left-ctx-∷ {A = A} {B = B}
      {p = p} {p′ = p↑} liftγ)
    (value ∷⊑∷ᶠ environment)
    with assumption-membership-unique→precision-index-unique
      (assumption-membership-unique-source unique)
      p↑ (⊑-source-liftνᵢ p)
left-abstract-framed-environment-lift
    {θ = θ} {X = X} {runtime↑ = runtime↑}
    unique
    (NTI.lift-left-ctx-∷ {A = A} {B = B}
      {p = p} {p′ = p↑} liftγ)
    (value ∷⊑∷ᶠ environment)
    | refl =
  left-lifted-value unique refl extension-refl
    lifted-typed lifted-operational value
    ∷⊑∷ᶠ
  left-abstract-framed-environment-lift unique liftγ environment
  where
  lifted-typed =
    typed-value-type-transport
      (sym (interpret-weaken
        (nominal-type (abstract-name X))
        (semanticEnvironment θ) A))
      refl
      (framed-value-typed value)

  lifted-operational =
    operational-value-type-transport
      (sym (interpret-weaken
        (nominal-type (abstract-name X))
        (semanticEnvironment θ) A))
      refl
      (framed-value-operational value)

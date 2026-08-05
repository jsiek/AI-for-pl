module proof.InterpreterTypeEnvironmentClosingProof where

-- File Charter:
--   * Extends static-assumption realization below closing type abstractions.
--   * Handles paired nominal allocation and source-only abstract binders.
--   * Contains no interpreter recursion, typing, or reduction argument.

open import Agda.Builtin.Equality using (refl)
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (zero; suc)
open import Data.Product using (_,_; Σ-syntax)

open import ImprecisionWf using
  ( ImpAssm
  ; ImpCtx
  ; _ˣ⊑★
  ; _ˣ⊑ˣ_
  ; ⇑ᵢ
  ; ⇑ᵢₐ
  ; ⇑ᴸᵢ
  ; ⇑ᴸᵢₐ
  )
open import Interpreter
open import Narrowing.InterpreterCoercionNarrowing using
  (InterpreterTypeNarrowing)
open import Simulation.Core.InterpreterSimulationContextProperties using
  (type-environment-realization-weaken)
open import Narrowing.InterpreterTermNarrowing
open import Runtime.InterpreterTypeEnvironmentRealization
open import Narrowing.InterpreterWorldNarrowing using
  ( TypeEnvironmentScoped
  ; abstract-scoped
  ; seal-scoped
  ; allocated
  )
import Narrowing.InterpreterWorldNarrowingProperties as WorldProperties
open import Types using (Ty)

open Narrowing.InterpreterTermNarrowing.RelatedWorlds

module WorldProof =
  WorldProperties.WorldNarrowingProperties
    InterpreterTypeNarrowing

paired-assumption-under-seals :
  ∀ {W W′}
    {R : WorldRelation W W′}
    {θ θ′ α α′ assumption} →
  AssumptionRealization R θ θ′ assumption →
  AssumptionRealization R
    (seal-name α ∷ θ) (seal-name α′ ∷ θ′)
    (⇑ᵢₐ assumption)
paired-assumption-under-seals
    (paired-assumption left-at right-at name~name′) =
  paired-assumption left-at right-at name~name′
paired-assumption-under-seals
    (source-dynamic-assumption left-at name-ok) =
  source-dynamic-assumption left-at name-ok

paired-assumptions-under-seals :
  ∀ {W W′}
    {R : WorldRelation W W′}
    {Φ θ θ′ α α′} →
  (∀ {assumption} →
    assumption ∈ Φ →
    AssumptionRealization R θ θ′ assumption) →
  ∀ {assumption} →
  assumption ∈ ⇑ᵢ Φ →
  AssumptionRealization R
    (seal-name α ∷ θ) (seal-name α′ ∷ θ′) assumption
paired-assumptions-under-seals {Φ = []} realizes ()
paired-assumptions-under-seals {Φ = assumption ∷ Φ}
    realizes (here refl) =
  paired-assumption-under-seals (realizes (here refl))
paired-assumptions-under-seals {Φ = assumption ∷ Φ}
    realizes (there member) =
  paired-assumptions-under-seals
    (λ old-member → realizes (there old-member))
    member

left-assumption-under-name :
  ∀ {W W′}
    {R : WorldRelation W W′}
    {θ θ′ name assumption} →
  AssumptionRealization R θ θ′ assumption →
  AssumptionRealization R
    (name ∷ θ) θ′ (⇑ᴸᵢₐ assumption)
left-assumption-under-name
    (paired-assumption left-at right-at name~name′) =
  paired-assumption left-at right-at name~name′
left-assumption-under-name
    (source-dynamic-assumption left-at name-ok) =
  source-dynamic-assumption left-at name-ok

left-assumptions-under-name :
  ∀ {W W′}
    {R : WorldRelation W W′}
    {Φ θ θ′ name} →
  (∀ {assumption} →
    assumption ∈ Φ →
    AssumptionRealization R θ θ′ assumption) →
  ∀ {assumption} →
  assumption ∈ ⇑ᴸᵢ Φ →
  AssumptionRealization R
    (name ∷ θ) θ′ assumption
left-assumptions-under-name {Φ = []} realizes ()
left-assumptions-under-name {Φ = assumption ∷ Φ}
    realizes (here refl) =
  left-assumption-under-name (realizes (here refl))
left-assumptions-under-name {Φ = assumption ∷ Φ}
    realizes (there member) =
  left-assumptions-under-name
    (λ old-member → realizes (there old-member))
    member

paired-seal-allocation-realization :
  ∀ {W W′ U U′ Φ θ θ′ A A′ σ σ′}
    {R : WorldRelation W W′}
    {S : WorldRelation U U′} →
  (R≤S : WorldExtension R S) →
  (A~A′ : InterpreterTypeNarrowing A A′) →
  (σ~σ′ : TypeEnvironmentNarrowing S σ σ′) →
  TypeEnvironmentRealization R Φ θ θ′ →
  TypeEnvironmentRealization
    (allocate-both S A~A′ σ~σ′)
    ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
    (seal-name (freshSealName U) ∷ θ)
    (seal-name (freshSealName U′) ∷ θ′)
paired-seal-allocation-realization
    {U = U} {U′} {Φ} {θ} {θ′} {A} {A′} {σ} {σ′}
    {R = R} {S}
    R≤S A~A′ σ~σ′ realization =
  type-environment-realization
    (seal-name⊑ link-here ∷⊑∷ᵗᵉ
      environments-narrow weakened)
    realize
  where
  weakened :
    TypeEnvironmentRealization
      (allocate-both S A~A′ σ~σ′) _ _ _
  weakened =
    type-environment-realization-weaken
      (extension-both R≤S) realization

  realize :
    ∀ {assumption} →
    assumption ∈ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ _) →
    AssumptionRealization
      (allocate-both S A~A′ σ~σ′)
      (seal-name (freshSealName U) ∷ _)
      (seal-name (freshSealName U′) ∷ _)
      assumption
  realize (here refl) =
    paired-assumption refl refl (seal-name⊑ link-here)
  realize (there member) =
    paired-assumptions-under-seals
      (realizes-assumption weakened) member

left-abstract-realization :
  ∀ {W W′ Φ θ θ′ X}
    {R : WorldRelation W W′} →
  TypeEnvironmentRealization R Φ θ θ′ →
  TypeEnvironmentRealization R
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
    (abstract-name X ∷ θ) θ′
left-abstract-realization {Φ = Φ} {θ} {θ′} {X} realization =
  type-environment-realization
    (abstract-scoped ∷ˡ⊑ᵗᵉ (environments-narrow realization))
    realize
  where
  realize :
    ∀ {assumption} →
    assumption ∈ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ _) →
    AssumptionRealization _ (abstract-name _ ∷ _) _ assumption
  realize (here refl) =
    source-dynamic-assumption refl source-dynamic-abstract
  realize (there member) =
    left-assumptions-under-name
      (realizes-assumption realization) member

left-dynamic-seal-allocation-realization-at :
  ∀ {W W′ U U′ Φ θ θ′ σ} {allocated-type : Ty}
    {R : WorldRelation W W′}
    {S : WorldRelation U U′} →
  (R≤S : WorldExtension R S) →
  (σ-ok : TypeEnvironmentScoped U σ) →
  TypeEnvironmentRealization R Φ θ θ′ →
  TypeEnvironmentRealization
    (allocate-left-dynamic {A = allocated-type} S σ-ok)
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
    (seal-name (freshSealName U) ∷ θ) θ′
left-dynamic-seal-allocation-realization-at
    {U = U} {Φ} {θ} {θ′} {allocated-type = A₀}
    R≤S σ-ok realization =
  type-environment-realization
    (seal-scoped (allocated (here refl)) ∷ˡ⊑ᵗᵉ
      environments-narrow allocated-realization)
    λ
      { (here refl) →
          source-dynamic-assumption refl
            (source-dynamic-seal left-dynamic-here)
      ; (there member) →
          left-assumptions-under-name
            (realizes-assumption allocated-realization)
            member
      }
  where
  allocated-realization =
    type-environment-realization-weaken
      (extension-left {A = A₀} extension-refl)
      (type-environment-realization-weaken R≤S realization)

left-dynamic-seal-allocation-realization :
  ∀ {W W′ U U′ Φ θ θ′} {allocated-type : Ty}
    {R : WorldRelation W W′}
    {S : WorldRelation U U′} →
  (R≤S : WorldExtension R S) →
  TypeEnvironmentRealization R Φ θ θ′ →
  Σ[ θ-ok ∈ TypeEnvironmentScoped U θ ]
    TypeEnvironmentRealization
      (allocate-left-dynamic {A = allocated-type} S θ-ok)
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      (seal-name (freshSealName U) ∷ θ) θ′
left-dynamic-seal-allocation-realization
    {U = U} {Φ} {θ} {θ′} {allocated-type = A₀}
    {R = R} {S}
    R≤S realization
    with type-environment-realization-weaken R≤S realization
left-dynamic-seal-allocation-realization
    {U = U} {Φ} {θ} {θ′} {allocated-type = A₀}
    {R = R} {S}
    R≤S realization
    | weakened
    with WorldProof.type-environment-left-scoped
      (environments-narrow weakened)
left-dynamic-seal-allocation-realization
    {U = U} {Φ} {θ} {θ′} {allocated-type = A₀}
    {R = R} {S}
    R≤S realization
    | weakened | θ-ok =
  θ-ok ,
  left-dynamic-seal-allocation-realization-at
    {allocated-type = A₀}
    R≤S θ-ok realization

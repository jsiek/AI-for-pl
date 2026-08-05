module Runtime.InterpreterTypeEnvironmentRealization where

-- File Charter:
--   * Connects static imprecision assumptions with concrete runtime type
--     environments and the proof-relevant world relation.
--   * Records paired-variable lookup and source-dynamic lookup explicitly.
--   * Contains no interpreter, coercion, or reduction argument.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using ([])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (just)
open import Data.Product using (_×_; Σ-syntax)

open import ImprecisionWf using
  (ImpAssm; ImpCtx; _ˣ⊑★; _ˣ⊑ˣ_)
open import Interpreter
open import Narrowing.InterpreterCoercionNarrowing using
  (InterpreterTypeNarrowing)
import Narrowing.InterpreterWorldNarrowing
open import Types using (TyVar)

module RelatedWorlds =
  Narrowing.InterpreterWorldNarrowing.WorldNarrowing
    InterpreterTypeNarrowing

open RelatedWorlds

data SourceDynamicName
    {W W′ : World}
    (R : WorldRelation W W′) :
    TypeName →
    Set₁ where
  source-dynamic-abstract :
    ∀ {X} →
    SourceDynamicName R (abstract-name X)

  source-dynamic-seal :
    ∀ {α} →
    LeftDynamicSeal R α →
    SourceDynamicName R (seal-name α)

data AssumptionRealization
    {W W′ : World}
    (R : WorldRelation W W′)
    (θ θ′ : TypeEnvironment) :
    ImpAssm → Set₁ where
  paired-assumption :
    ∀ {X X′ name name′} →
    lookup θ X ≡ just name →
    lookup θ′ X′ ≡ just name′ →
    TypeNameNarrowing R name name′ →
    AssumptionRealization R θ θ′ (X ˣ⊑ˣ X′)

  source-dynamic-assumption :
    ∀ {X name} →
    lookup θ X ≡ just name →
    SourceDynamicName R name →
    AssumptionRealization R θ θ′ (X ˣ⊑★)

record TypeEnvironmentRealization
    {W W′ : World}
    (R : WorldRelation W W′)
    (Φ : ImpCtx)
    (θ θ′ : TypeEnvironment) : Set₁ where
  constructor type-environment-realization
  field
    environments-narrow :
      TypeEnvironmentNarrowing R θ θ′

    realizes-assumption :
      ∀ {assumption} →
      assumption ∈ Φ →
      AssumptionRealization R θ θ′ assumption

open TypeEnvironmentRealization public

empty-type-environment-realization :
  ∀ {W W′}
    {R : WorldRelation W W′} →
  TypeEnvironmentRealization R [] [] []
empty-type-environment-realization =
  type-environment-realization []⊑[]ᵗᵉ (λ ())

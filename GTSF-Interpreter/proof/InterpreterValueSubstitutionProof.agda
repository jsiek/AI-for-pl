module proof.InterpreterValueSubstitutionProof where

-- File Charter:
--   * Proves that paired fresh-name substitution preserves semantic value
--     narrowing.
--   * Handles captured type environments and one-sided wrapper scopes.
--   * Uses the paired allocation itself as the new seal correspondence link.

open import Agda.Builtin.Equality using (refl)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Nullary using (yes; no)

open import Interpreter
import InterpreterEnvironmentNarrowing as EnvironmentProperties
open import InterpreterValueNarrowing
open import InterpreterWorldNarrowing
import InterpreterWorldNarrowingProperties as WorldProperties

module ValueSubstitutionProof
  (leaves : NarrowingLeaves)
  where

  module Values = ValueNarrowing leaves
  open Values
  open Values.RelatedWorlds

  module Environments =
    EnvironmentProperties.EnvironmentNarrowing leaves

  module WorldProof =
    WorldProperties.WorldNarrowingProperties (TypeNarrowing leaves)

  replace-name-narrowing :
    ∀ {W W′ A A′ θ θ′ σ σ′ X}
      {R : WorldRelation W W′} →
    (A~A′ : TypeNarrowing leaves A A′) →
    (θ~θ′ : TypeEnvironmentNarrowing R θ θ′) →
    TypeEnvironmentNarrowing R σ σ′ →
    TypeEnvironmentNarrowing
      (allocate-both R A~A′ θ~θ′)
      (replaceName X (freshSealName W) σ)
      (replaceName X (freshSealName W′) σ′)
  replace-name-narrowing A~A′ θ~θ′ []⊑[]ᵗᵉ =
    []⊑[]ᵗᵉ
  replace-name-narrowing {X = X} A~A′ θ~θ′
      (abstract-name⊑ {X = Y} ∷⊑∷ᵗᵉ σ~σ′)
      with X ≟Name Y
  replace-name-narrowing {X = X} A~A′ θ~θ′
      (abstract-name⊑ {X = .X} ∷⊑∷ᵗᵉ σ~σ′)
      | yes refl =
    seal-name⊑ link-here ∷⊑∷ᵗᵉ
      replace-name-narrowing A~A′ θ~θ′ σ~σ′
  replace-name-narrowing {X = X} A~A′ θ~θ′
      (abstract-name⊑ {X = Y} ∷⊑∷ᵗᵉ σ~σ′)
      | no X≢Y =
    abstract-name⊑ ∷⊑∷ᵗᵉ
      replace-name-narrowing A~A′ θ~θ′ σ~σ′
  replace-name-narrowing A~A′ θ~θ′
      (seal-name⊑ α~α′ ∷⊑∷ᵗᵉ σ~σ′) =
    seal-name⊑ (link-under-both α~α′) ∷⊑∷ᵗᵉ
      replace-name-narrowing A~A′ θ~θ′ σ~σ′

  replace-name-left-scoped :
    ∀ {W W′ A A′ θ θ′ σ X}
      {R : WorldRelation W W′} →
    (A~A′ : TypeNarrowing leaves A A′) →
    (θ~θ′ : TypeEnvironmentNarrowing R θ θ′) →
    TypeEnvironmentScoped W σ →
    TypeEnvironmentScoped
      (allocate W A θ)
      (replaceName X (freshSealName W) σ)
  replace-name-left-scoped A~A′ θ~θ′ []-scoped =
    []-scoped
  replace-name-left-scoped {X = X} A~A′ θ~θ′
      (abstract-scoped {X = Y} ∷-scoped σ-ok)
      with X ≟Name Y
  replace-name-left-scoped {X = X} A~A′ θ~θ′
      (abstract-scoped {X = .X} ∷-scoped σ-ok)
      | yes refl =
    seal-scoped (allocated (here refl)) ∷-scoped
      replace-name-left-scoped A~A′ θ~θ′ σ-ok
  replace-name-left-scoped {X = X} A~A′ θ~θ′
      (abstract-scoped {X = Y} ∷-scoped σ-ok)
      | no X≢Y =
    abstract-scoped ∷-scoped
      replace-name-left-scoped A~A′ θ~θ′ σ-ok
  replace-name-left-scoped A~A′ θ~θ′
      (seal-scoped (allocated α∈W) ∷-scoped σ-ok) =
    seal-scoped (allocated (there α∈W)) ∷-scoped
      replace-name-left-scoped A~A′ θ~θ′ σ-ok

  replace-name-right-scoped :
    ∀ {W W′ A A′ θ θ′ σ′ X}
      {R : WorldRelation W W′} →
    (A~A′ : TypeNarrowing leaves A A′) →
    (θ~θ′ : TypeEnvironmentNarrowing R θ θ′) →
    TypeEnvironmentScoped W′ σ′ →
    TypeEnvironmentScoped
      (allocate W′ A′ θ′)
      (replaceName X (freshSealName W′) σ′)
  replace-name-right-scoped A~A′ θ~θ′ []-scoped =
    []-scoped
  replace-name-right-scoped {X = X} A~A′ θ~θ′
      (abstract-scoped {X = Y} ∷-scoped σ′-ok)
      with X ≟Name Y
  replace-name-right-scoped {X = X} A~A′ θ~θ′
      (abstract-scoped {X = .X} ∷-scoped σ′-ok)
      | yes refl =
    seal-scoped (allocated (here refl)) ∷-scoped
      replace-name-right-scoped A~A′ θ~θ′ σ′-ok
  replace-name-right-scoped {X = X} A~A′ θ~θ′
      (abstract-scoped {X = Y} ∷-scoped σ′-ok)
      | no X≢Y =
    abstract-scoped ∷-scoped
      replace-name-right-scoped A~A′ θ~θ′ σ′-ok
  replace-name-right-scoped A~A′ θ~θ′
      (seal-scoped (allocated α′∈W′) ∷-scoped σ′-ok) =
    seal-scoped (allocated (there α′∈W′)) ∷-scoped
      replace-name-right-scoped A~A′ θ~θ′ σ′-ok

  substitute-name-preserves-value-narrowing :
    ∀ {W W′ A A′ θ θ′ X V V′}
      {R : WorldRelation W W′} →
    (A~A′ : TypeNarrowing leaves A A′) →
    (θ~θ′ : TypeEnvironmentNarrowing R θ θ′) →
    ValueNarrowing R V V′ →
    ValueNarrowing
      (allocate-both R A~A′ θ~θ′)
      (substituteName X (freshSealName W) V)
      (substituteName X (freshSealName W′) V′)
  substitute-name-preserves-value-narrowing A~A′ θ~θ′
      (closure⊑ N~N′ γ~γ′ σ~σ′) =
    closure⊑ N~N′
      (Environments.environment-narrowing-weaken
        (extension-both extension-refl) γ~γ′)
      (replace-name-narrowing A~A′ θ~θ′ σ~σ′)
  substitute-name-preserves-value-narrowing A~A′ θ~θ′
      (constant⊑ κ) =
    constant⊑ κ
  substitute-name-preserves-value-narrowing A~A′ θ~θ′
      (tagged⊑ G~H σ~σ′ V~V′) =
    tagged⊑ G~H
      (replace-name-narrowing A~A′ θ~θ′ σ~σ′)
      (substitute-name-preserves-value-narrowing
        A~A′ θ~θ′ V~V′)
  substitute-name-preserves-value-narrowing A~A′ θ~θ′
      (sealed⊑ α~α′ V~V′) =
    sealed⊑ (link-under-both α~α′)
      (substitute-name-preserves-value-narrowing
        A~A′ θ~θ′ V~V′)
  substitute-name-preserves-value-narrowing A~A′ θ~θ′
      (function-proxy⊑ p~p′ q~q′ σ~σ′ V~V′) =
    function-proxy⊑ p~p′ q~q′
      (replace-name-narrowing A~A′ θ~θ′ σ~σ′)
      (substitute-name-preserves-value-narrowing
        A~A′ θ~θ′ V~V′)
  substitute-name-preserves-value-narrowing
      {X = X} A~A′ θ~θ′
      (type-abstraction⊑ {X = Y} V~V′)
      with X ≟Name Y
  substitute-name-preserves-value-narrowing
      {X = X} A~A′ θ~θ′
      (type-abstraction⊑ {X = .X} V~V′)
      | yes refl =
    type-abstraction⊑
      (Environments.value-narrowing-weaken
        (extension-both extension-refl) V~V′)
  substitute-name-preserves-value-narrowing
      {X = X} A~A′ θ~θ′
      (type-abstraction⊑ {X = Y} V~V′)
      | no X≢Y =
    type-abstraction⊑
      (substitute-name-preserves-value-narrowing
        A~A′ θ~θ′ V~V′)
  substitute-name-preserves-value-narrowing A~A′ θ~θ′
      (forall-proxy⊑ c~c′ σ~σ′ V~V′) =
    forall-proxy⊑ c~c′
      (replace-name-narrowing A~A′ θ~θ′ σ~σ′)
      (substitute-name-preserves-value-narrowing
        A~A′ θ~θ′ V~V′)
  substitute-name-preserves-value-narrowing A~A′ θ~θ′
      (generalized⊑ B~B′ c~c′ σ~σ′ V~V′) =
    generalized⊑ B~B′ c~c′
      (replace-name-narrowing A~A′ θ~θ′ σ~σ′)
      (substitute-name-preserves-value-narrowing
        A~A′ θ~θ′ V~V′)
  substitute-name-preserves-value-narrowing A~A′ θ~θ′
      (left-tagged⊑ boundary σ-ok V~V′) =
    left-tagged⊑ boundary
      (replace-name-left-scoped A~A′ θ~θ′ σ-ok)
      (substitute-name-preserves-value-narrowing
        A~A′ θ~θ′ V~V′)
  substitute-name-preserves-value-narrowing A~A′ θ~θ′
      (right-tagged⊑ boundary σ′-ok V~V′) =
    right-tagged⊑ boundary
      (replace-name-right-scoped A~A′ θ~θ′ σ′-ok)
      (substitute-name-preserves-value-narrowing
        A~A′ θ~θ′ V~V′)
  substitute-name-preserves-value-narrowing A~A′ θ~θ′
      (left-function-proxy⊑ boundary σ-ok V~V′) =
    left-function-proxy⊑ boundary
      (replace-name-left-scoped A~A′ θ~θ′ σ-ok)
      (substitute-name-preserves-value-narrowing
        A~A′ θ~θ′ V~V′)
  substitute-name-preserves-value-narrowing A~A′ θ~θ′
      (right-function-proxy⊑ boundary σ′-ok V~V′) =
    right-function-proxy⊑ boundary
      (replace-name-right-scoped A~A′ θ~θ′ σ′-ok)
      (substitute-name-preserves-value-narrowing
        A~A′ θ~θ′ V~V′)
  substitute-name-preserves-value-narrowing A~A′ θ~θ′
      (left-forall-proxy⊑ boundary σ-ok V~V′) =
    left-forall-proxy⊑ boundary
      (replace-name-left-scoped A~A′ θ~θ′ σ-ok)
      (substitute-name-preserves-value-narrowing
        A~A′ θ~θ′ V~V′)
  substitute-name-preserves-value-narrowing A~A′ θ~θ′
      (right-forall-proxy⊑ boundary σ′-ok V~V′) =
    right-forall-proxy⊑ boundary
      (replace-name-right-scoped A~A′ θ~θ′ σ′-ok)
      (substitute-name-preserves-value-narrowing
        A~A′ θ~θ′ V~V′)
  substitute-name-preserves-value-narrowing A~A′ θ~θ′
      (left-generalized⊑ boundary σ-ok V~V′) =
    left-generalized⊑ boundary
      (replace-name-left-scoped A~A′ θ~θ′ σ-ok)
      (substitute-name-preserves-value-narrowing
        A~A′ θ~θ′ V~V′)
  substitute-name-preserves-value-narrowing A~A′ θ~θ′
      (right-generalized⊑ boundary σ′-ok V~V′) =
    right-generalized⊑ boundary
      (replace-name-right-scoped A~A′ θ~θ′ σ′-ok)
      (substitute-name-preserves-value-narrowing
        A~A′ θ~θ′ V~V′)

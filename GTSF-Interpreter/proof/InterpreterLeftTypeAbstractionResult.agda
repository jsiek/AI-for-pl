module proof.InterpreterLeftTypeAbstractionResult where

-- File Charter:
--   * Wraps an exact source-value/target-value result below an abstract name
--     into the source-only type-abstraction result at the outer runtime.
--   * Stores a future instantiation callback by transporting the exact body
--     origin from the abstract name to each freshly allocated seal.
--   * Uses closing, typing, world extension, and narrowing metatheory only.

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (_∷_; map)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (suc; zero)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import ImprecisionWf using
  (_ˣ⊑★; ⇑ᴸᵢ; _∣_⊢_⊑_⊣_; ν)
open import Interpreter
open import Narrowing.InterpreterCoercionNarrowing using
  (left-type-abstraction-boundary; type-narrowing)
open import Runtime.InterpreterClosedValue
open import Simulation.Framed.InterpreterFramedNameInstantiation
open import Narrowing.InterpreterFramedValueNarrowing
open import Narrowing.InterpreterFramedValueNarrowingProperties
open import Runtime.InterpreterOperationalNameInstantiation
open import Narrowing.InterpreterOperationalValueNarrowing
open import Typing.InterpreterSemanticTyping
open import Typing.InterpreterSemanticTypingCore
open import Simulation.Core.InterpreterSimulationContext
open import Simulation.Core.InterpreterSimulationContextProperties using
  (left-world-extension; right-world-extension;
   runtime-narrowing-weaken)
open import Narrowing.InterpreterTermNarrowing
open import Narrowing.InterpreterTypedValueNarrowing
open import Narrowing.InterpreterValueNarrowing
open import Narrowing.InterpreterWorldNarrowing using
  (TypeEnvironmentScoped; allocated)
import NuTermImprecision as NTI
open import
  proof.NuImprecisionAssumptionMembershipUniquenessProof using
  (assumption-membership-unique-source)
import NuTerms as N
import TermTyping as TT
open import proof.InterpreterCloseValueTyping using
  (closedValue-typing)
open import proof.InterpreterClosingRuntimeFrame using
  (left-closing-runtime-frame)
open import proof.InterpreterClosedValueProof using
  (replaceName-head)
open import proof.InterpreterOperationalEnvironmentLift using
  (operational-value-type-transport)
open import proof.InterpreterSemanticTypingProperties using
  (allocated-here; environment-type-weaken;
   environment-weaken; instantiate-interpret)
import Runtime.InterpreterRuntimeFrame as Frame
open import Types

open Narrowing.InterpreterTermNarrowing.InterpreterValues
open Narrowing.InterpreterTermNarrowing.RelatedWorlds

left-type-abstraction-result :
  ∀ {W W′ U U′ Φ Δᴸ Δᴿ ρ ρ↑ γᵀ γᵀ↑
      θ θ′ γ γ′ X V N′ A B p U-body Q}
    {{nonvar : ImprecisionWf.NonVar A}}
    {occ : occurs zero A ≡ true}
    {R : WorldRelation W W′}
    {relation : WorldRelation U U′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  (store :
    NTI.LiftLeftStoreⁱ
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ↑) →
  (context :
    NTI.LiftLeftCtxⁱ
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) γᵀ γᵀ↑) →
  (vV : N.Value V) →
  (termV : InterpreterTerm V) →
  (termN′ : InterpreterTerm N′) →
  (body :
    AlignedInterpreterTermNarrowing
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      (suc Δᴸ) Δᴿ ρ↑ γᵀ↑ V N′ A B p) →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  (fresh : abstract-name X ∉ θ) →
  (closed : ClosedValue γ (abstract-name X ∷ θ) vV U-body) →
  WorldExtension R relation →
  FramedValueResult
    ρ↑ (abstract-name X ∷ θ) θ′ p relation U-body Q →
  FramedValueResult
    ρ θ θ′ (ν nonvar occ p) relation
    (type-abstraction X U-body) Q
left-type-abstraction-result
    {W = W} {W′} {U} {U′} {Φ} {Δᴸ} {Δᴿ}
    {ρ} {ρ↑} {γᵀ} {γᵀ↑} {θ} {θ′} {γ} {γ′}
    {X} {V} {N′} {A} {B} {p} {U-body} {Q}
    {{nonvar = nonvar}} {occ = occ} {R = R}
    {relation = relation}
    {runtime = runtime}
    store context vV termV termN′ body environment fresh closed
    R≤S (framed-result body-runtime body-value) =
  framed-result outer-runtime
    (framed-value outer-typed outer-operational outer-origin)
  where
  body-typed =
    framed-value-typed body-value

  terms =
    open-interpreter-narrowing {R = relation} body

  source-body-scoped =
    semantic-value-scoped (left-value-typed body-typed)

  target-scoped =
    semantic-value-scoped (right-value-typed body-typed)

  instantiate-values :
    ∀ {Z Z′ C σ}
      {T : WorldRelation Z Z′} →
    WorldExtension relation T →
    (σ-ok :
      TypeEnvironmentScoped Z σ) →
    ValueNarrowing
      (allocate-left-dynamic {A = C} T σ-ok)
      (substituteName X (freshSealName Z) U-body) Q
  instantiate-values
      {C = source-type} {σ = type-environment}
      S≤T σ-ok =
    left-name-instantiated⊑
      (extension-left
        {A = source-type} {θ = type-environment}
        {θ-ok = σ-ok} S≤T)
      allocated-here refl
      (values-narrow body-typed)

  outer-values =
    left-type-abstraction⊑
      (left-type-abstraction-boundary
        (type-narrowing (ν nonvar occ p)))
      (related-left-type-abstraction
        source-body-scoped target-scoped instantiate-values)

  outer-runtime =
    runtime-narrowing-weaken R≤S
      (left-world-typed body-typed)
      (right-world-typed body-typed)
      runtime

  outer-closed =
    closed-type-abstraction fresh closed

  outer-alignment =
    left-type-abstraction-aligned
      occ store context vV termV termN′ body

  outer-left-typed-at-base =
    closedValue-typing
      (left-world-typed runtime)
      (left-runtime-context runtime)
      (left-environment-typed environment)
      (interpreter-narrowing-source-term
        (aligned-term-shape outer-alignment))
      (TT.forget
        (open-interpreter-narrowing-source-typing
          (open-interpreter-narrowing
            {R = R} outer-alignment)))
      outer-closed

  outer-left-typed =
    semantic-value-world-weaken
      (left-world-extension R≤S)
      (left-world-typed body-typed)
      outer-left-typed-at-base

  outer-typed =
    typed-value-narrowing outer-values
      (left-world-typed body-typed)
      (right-world-typed body-typed)
      outer-left-typed
      (right-value-typed body-typed)

  source-environment :
    ∀ {Z Z′ C σ}
      {T : WorldRelation Z Z′}
      (S≤T :
        WorldExtension relation T)
      (σ-ok :
        TypeEnvironmentScoped Z σ)
      (allocated-runtime :
        RuntimeNarrowing
          (allocate-left-dynamic {A = C} T σ-ok)
          ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
          (suc Δᴸ) Δᴿ ρ↑
          (seal-name (freshSealName Z) ∷ θ) θ′) →
    EnvironmentTyping
      (allocate Z C σ)
      (seal-name (freshSealName Z) ∷ θ)
      γ (NTI.leftCtxⁱ γᵀ↑)
  source-environment
      {Z = z-world} {C = source-type}
      {σ = type-environment}
      S≤T σ-ok allocated-runtime =
    subst
      (EnvironmentTyping
        _ (seal-name (freshSealName z-world) ∷ θ) γ)
      (sym (NTI.leftCtxⁱ-lift-left context))
      (environment-type-weaken
        (seal-name (freshSealName z-world))
        (environment-weaken
          (left-world-extension
            (extension-left
              {A = source-type} {θ = type-environment}
              {θ-ok = σ-ok}
              (PersistentWorldProperties.world-extension-trans R≤S S≤T)))
          (left-world-typed allocated-runtime)
          (left-environment-typed environment)))

  instantiated-typed :
    ∀ {Z Z′ C σ}
      {T : WorldRelation Z Z′}
      (S≤T :
        WorldExtension relation T)
      (σ-ok :
        TypeEnvironmentScoped Z σ)
      (allocated-runtime :
        RuntimeNarrowing
          (allocate-left-dynamic {A = C} T σ-ok)
          ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
          (suc Δᴸ) Δᴿ ρ↑
          (seal-name (freshSealName Z) ∷ θ) θ′) →
    TypedValueNarrowing
      ⟦ A ⟧[ seal-name (freshSealName Z) ∷ θ ]
      ⟦ B ⟧[ θ′ ]
      (allocate-left-dynamic {A = C} T σ-ok)
      (substituteName X (freshSealName Z) U-body) Q
  instantiated-typed
      {C = source-type} {σ = type-environment}
      S≤T σ-ok allocated-runtime =
    typed-value-narrowing
      (instantiate-values S≤T σ-ok)
      (left-world-typed allocated-runtime)
      (right-world-typed allocated-runtime)
      (substituteName-closedValue-typing
        (left-world-typed allocated-runtime)
        (left-runtime-context allocated-runtime)
        (source-environment S≤T σ-ok allocated-runtime)
        termV
        (TT.forget
          (open-interpreter-narrowing-source-typing terms))
        (here refl)
        (replaceName-head fresh)
        closed)
      (semantic-value-world-weaken
        (right-world-extension
          (extension-left
            {A = source-type} {θ = type-environment}
            {θ-ok = σ-ok}
            S≤T))
        (right-world-typed allocated-runtime)
        (right-value-typed body-typed))

  instantiate-framed :
    ∀ {Z Z′ C σ}
      {T : WorldRelation Z Z′} →
    (S≤T :
      WorldExtension relation T) →
    (σ-ok :
      TypeEnvironmentScoped Z σ) →
    (allocated-runtime :
      RuntimeNarrowing
        (allocate-left-dynamic {A = C} T σ-ok)
        ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        (suc Δᴸ) Δᴿ ρ↑
        (seal-name (freshSealName Z) ∷ θ) θ′) →
    FramedValueNarrowing
      {A = A} {A′ = B} {p = p} allocated-runtime
      (substituteName X (freshSealName Z) U-body) Q
  instantiate-framed
      {C = source-type} {σ = type-environment}
      S≤T σ-ok allocated-runtime =
    left-name-instantiated-framed
      (instantiated-typed S≤T σ-ok allocated-runtime)
      (extension-left
        {A = source-type} {θ = type-environment}
        {θ-ok = σ-ok} S≤T)
      allocated-here refl
      body-value

  instantiate-operational :
    ∀ {Z Z′ C σ}
      {T : WorldRelation Z Z′} →
    WorldExtension relation T →
    (σ-ok :
      TypeEnvironmentScoped Z σ) →
    WorldTyping (allocate Z C σ) →
    WorldTyping Z′ →
    OperationalValueNarrowing
      (instantiateSemantic
        (nominal-type
          (seal-name (freshSealName Z)))
        (interpretType
          (bound-type zero ∷
            map liftSemantic
              (semanticEnvironment θ))
          A))
      ⟦ B ⟧[ θ′ ]
      (allocate-left-dynamic {A = C} T σ-ok)
      (substituteName X (freshSealName Z) U-body) Q
  instantiate-operational
      {Z = z-world} {C = source-type}
      {σ = type-environment}
      S≤T σ-ok z-world⊢ target-world⊢ =
    operational-value-type-transport
      (sym (instantiate-interpret
        (nominal-type (seal-name (freshSealName z-world)))
        θ A))
      refl
      (left-name-instantiated-operational
        (instantiated-typed S≤T σ-ok allocated-runtime)
        (extension-left
          {A = source-type} {θ = type-environment}
          {θ-ok = σ-ok}
          S≤T)
        allocated-here refl
        (framed-value-operational body-value))
    where
    R≤T =
      PersistentWorldProperties.world-extension-trans R≤S S≤T

    allocated-frame =
      left-closing-runtime-frame
        (runtime-narrowing-frame runtime)
        R≤T σ-ok store

    allocated-runtime =
      runtime-narrowing-from-frame z-world⊢ target-world⊢
        (assumption-membership-unique-source
          (assumption-membership-unique runtime))
        allocated-frame

  outer-operational =
    operational-value outer-typed
      (left-type-abstraction-origin instantiate-operational)

  outer-origin =
    left-type-abstraction-originᶠ store instantiate-framed

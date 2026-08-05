module proof.InterpreterCloseValueNarrowingProof where

-- File Charter:
--   * Proves that closing aligned syntactic values preserves value narrowing.
--   * Constructs paired type-abstraction evidence extensionally after fresh
--     seal allocation, without equating concrete abstract binder names.
--   * Constructs source-only abstraction evidence for every future left
--     allocation scope.
--   * Contains no evaluator call or reduction argument.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using (_∷_)
open import Data.Maybe using (just)
open import Data.Nat using (_≤_; suc; s≤s)
open import Data.Nat.Properties using (n≤1+n; ≤-trans)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import ImprecisionWf using
  (_∣_⊢_⊑_⊣_; ν)
open import Interpreter
open import Runtime.InterpreterClosedValue
open import Runtime.InterpreterClosedValueFrame
open import Runtime.InterpreterClosedValueProperties
open import Narrowing.InterpreterCoercionNarrowing using
  ( InterpreterTypeNarrowing
  ; type-narrowing
  ; left-type-abstraction-boundary
  ; right-function-proxy-boundary
  ; right-static-widening-action
  ; right-narrowing-action
  )
open import Narrowing.InterpreterEnvironmentNarrowing
open import Narrowing.InterpreterQuotientValueNarrowing using
  (quotient-value-frame)
import Runtime.InterpreterRuntimeFrame as Frame
open import Typing.InterpreterSemanticTypingCore using
  (EnvironmentTyping; WorldTyping)
open import Narrowing.InterpreterTermNarrowing
open import Runtime.InterpreterTypeEnvironmentClosing
open import Runtime.InterpreterTypeEnvironmentRealization
open import Narrowing.InterpreterWorldNarrowing using
  (TypeEnvironmentScoped; abstract-scoped; _∷-scoped_)
import Narrowing.InterpreterWorldNarrowingProperties as WorldProperties
import NuTermImprecision as NTI
import NuTerms as N
open import TermTyping using (cast-tag-or-id)
open import Types
open import proof.InterpreterClosedValueProof using
  (closeValue-closed)
open import proof.InterpreterClosingRuntimeFrame
open import proof.InterpreterRuntimeFramePrefix using
  (runtime-frame-prefix)
import proof.InterpreterSemanticTypingProperties as SemanticProof

open InterpreterValues
open Narrowing.InterpreterTermNarrowing.RelatedWorlds

module EnvironmentProof =
  Narrowing.InterpreterEnvironmentNarrowing.EnvironmentNarrowing
    interpreterNarrowingLeaves

module WorldProof =
  WorldProperties.WorldNarrowingProperties
    InterpreterTypeNarrowing

close-aligned-values :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ γᵀ M M′ A B p}
    {R : WorldRelation W W′}
    {γ γ′ θ θ′ U U′}
    {vM : N.Value M} {vM′ : N.Value M′} →
  AlignedInterpreterTermNarrowing
    Φ Δᴸ Δᴿ ρ γᵀ M M′ A B p →
  Frame.RuntimeFrameNarrowing R Φ Δᴸ Δᴿ ρ θ θ′ →
  (∀ {Z Z′}
     {S : WorldRelation Z Z′} →
    WorldExtension R S →
    WorldTyping Z →
    EnvironmentTyping Z θ γ (NTI.leftCtxⁱ γᵀ)) →
  (∀ {Z Z′}
     {S : WorldRelation Z Z′} →
    WorldExtension R S →
    WorldTyping Z′ →
    EnvironmentTyping Z′ θ′ γ′ (NTI.rightCtxⁱ γᵀ)) →
  TypeEnvironmentRealization R Φ θ θ′ →
  EnvironmentNarrowing R γ γ′ →
  nextAbstractIndex θ′ ≤ nextAbstractIndex θ →
  ClosedValue γ θ vM U →
  ClosedValue γ′ θ′ vM′ U′ →
  ValueNarrowing R U U′
close-aligned-values
    {R = R}
    (closure-aligned hA hA′ body)
    runtime left-env right-env realization γ~γ′ supply
    closed-closure closed-closure =
  closure⊑
    (persistent-body-narrowing
      (open-interpreter-narrowing {R = R} body)
      runtime left-env right-env)
    γ~γ′ (environments-narrow realization)
close-aligned-values
    {R = R} {γ = γ} {γ′} {θ} {θ′}
    {vM = N.Λ left-syntax} {vM′ = N.Λ right-syntax}
    (paired-type-abstraction-aligned
      store context vV vV′ termV termV′ body)
    runtime left-env right-env realization γ~γ′ supply
    (closed-type-abstraction
      {V = _} {U = V} {X = X} {vV = left-syntax}
      left-fresh left-body)
    (closed-type-abstraction
      {V = _} {U = V′} {X = X′} {vV = right-syntax}
      right-fresh right-body) =
  type-abstraction⊑
    (related-type-abstraction
      (closed-value-scoped
        (proj₁ (EnvironmentProof.environment-narrowing-scoped γ~γ′))
        (abstract-scoped ∷-scoped
          WorldProof.type-environment-left-scoped
            (environments-narrow realization))
        left-body)
      (closed-value-scoped
        (proj₂ (EnvironmentProof.environment-narrowing-scoped γ~γ′))
        (abstract-scoped ∷-scoped
          WorldProof.type-environment-right-scoped
            (environments-narrow realization))
        right-body)
      instantiate)
  where
  instantiate :
    ∀ {Z Z′ C C′ σ σ′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    (C~C′ : InterpreterTypeNarrowing C C′) →
    (σ~σ′ : TypeEnvironmentNarrowing S σ σ′) →
    ValueNarrowing
      (allocate-both S C~C′ σ~σ′)
      (substituteName X (freshSealName Z) V)
      (substituteName X′ (freshSealName Z′) V′)
  instantiate {Z = z} {Z′ = z′} R≤S C~C′ σ~σ′ =
    close-aligned-values
      body
      (paired-closing-runtime-frame
        runtime R≤S C~C′ σ~σ′ store)
      (λ allocated≤T T⊢ →
        subst
          (EnvironmentTyping _
            (seal-name (freshSealName z) ∷ θ) γ)
          (sym (NTI.leftCtxⁱ-lift context))
          (SemanticProof.environment-type-weaken
            (seal-name (freshSealName z))
            (left-env
              (WorldProof.world-extension-trans
                (extension-both R≤S) allocated≤T)
              T⊢)))
      (λ allocated≤T T⊢ →
        subst
          (EnvironmentTyping _
            (seal-name (freshSealName z′) ∷ θ′) γ′)
          (sym (NTI.rightCtxⁱ-lift context))
          (SemanticProof.environment-type-weaken
            (seal-name (freshSealName z′))
            (right-env
              (WorldProof.world-extension-trans
                (extension-both R≤S) allocated≤T)
              T⊢)))
      (paired-seal-allocation-realization
        R≤S C~C′ σ~σ′ realization)
      (EnvironmentProof.environment-narrowing-weaken
        (extension-both R≤S) γ~γ′)
      (s≤s supply)
      (closed-value-instantiate-head
        left-fresh left-body)
      (closed-value-instantiate-head
        right-fresh right-body)
close-aligned-values
    {R = R} {γ = γ} {γ′} {θ = θ} {θ′}
    {U′ = Q}
    {vM = N.Λ left-syntax}
    (left-type-abstraction-aligned
      {A = A-body} {p = p-body} {{safe = safe}}
      occ store context vV termV termN′ body)
    runtime left-env right-env realization γ~γ′ supply
    (closed-type-abstraction
      {U = V} {X = type-name X} {vV = left-syntax}
      left-fresh left-body)
    right-value =
  left-type-abstraction⊑
    (left-type-abstraction-boundary
      (type-narrowing (ν safe occ p-body)))
    (related-left-type-abstraction
      (closed-value-scoped
        (proj₁ (EnvironmentProof.environment-narrowing-scoped γ~γ′))
        (abstract-scoped ∷-scoped
          WorldProof.type-environment-left-scoped
            (environments-narrow realization))
        left-body)
      (closed-value-scoped
        (proj₂ (EnvironmentProof.environment-narrowing-scoped γ~γ′))
        (WorldProof.type-environment-right-scoped
          (environments-narrow realization))
        right-value)
      instantiate)
  where
  instantiate :
    ∀ {Z Z′ C σ}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    (σ-ok : TypeEnvironmentScoped Z σ) →
    ValueNarrowing
      (allocate-left-dynamic {A = C} S σ-ok)
      (substituteName (type-name X) (freshSealName Z) V)
      Q
  instantiate {Z = z} R≤S σ-ok =
    close-aligned-values
      body
      (left-closing-runtime-frame runtime R≤S σ-ok store)
      (λ allocated≤T T⊢ →
        subst
          (EnvironmentTyping _
            (seal-name (freshSealName z) ∷ θ) γ)
          (sym (NTI.leftCtxⁱ-lift-left context))
          (SemanticProof.environment-type-weaken
            (seal-name (freshSealName z))
            (left-env
              (WorldProof.world-extension-trans
                (extension-left R≤S) allocated≤T)
              T⊢)))
      (λ allocated≤T T⊢ →
        subst
          (EnvironmentTyping _ θ′ γ′)
          (sym (NTI.rightCtxⁱ-lift-left context))
          (right-env
            (WorldProof.world-extension-trans
              (extension-left R≤S) allocated≤T)
            T⊢))
      (left-dynamic-seal-allocation-realization-at
        R≤S σ-ok realization)
      (EnvironmentProof.environment-narrowing-weaken
        (extension-left R≤S) γ~γ′)
      (≤-trans supply (n≤1+n (nextAbstractIndex θ)))
      (closed-value-instantiate-head
        left-fresh left-body)
      right-value
close-aligned-values
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {ρ = ρ} {γᵀ = γᵀ}
    {R = R} {γ = γ} {γ′ = γ′} {θ = θ} {θ′ = θ′}
    {U = U} {U′ = U′}
    (allocation-prefix-aligned prefix body source target)
    runtime left-env right-env realization γ~γ′ supply
    left-value right-value =
  close-aligned-values
    body (runtime-frame-prefix prefix runtime)
    left-env right-env realization γ~γ′ supply
    left-value right-value
close-aligned-values
    constant-aligned
    runtime left-env right-env realization γ~γ′ supply
    (closed-constant κ) (closed-constant .κ) =
  constant⊑ κ
close-aligned-values
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {ρ = ρ} {γᵀ = γᵀ}
    {R = R} {γ = γ} {γ′ = γ′} {θ = θ} {θ′ = θ′}
    {U = U} {U′ = U′}
    {vM =
      (left-syntax N.⟨ left-down-inert ⟩)
        N.⟨ left-up-inert ⟩}
    {vM′ =
      (right-syntax N.⟨ right-down-inert ⟩)
        N.⟨ right-up-inert ⟩}
    (quotient-up-aligned
      {A = A} {A′ = A′} {D = D} {D′ = D′}
      {u = u} {u′ = u′}
      (quotient-down-aligned
        {C = C} {C′ = C′} {D = D} {D′ = D′}
        {d = d} {d′ = d′}
        source-down target-down body D⊑E alignment)
      widening pA)
    runtime left-env right-env realization γ~γ′ supply
    left-final right-final
    with closed-value-inert-frame left-final
       | closed-value-inert-frame right-final
close-aligned-values
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {ρ = ρ} {γᵀ = γᵀ}
    {R = R} {γ = γ} {γ′ = γ′} {θ = θ} {θ′ = θ′}
    {U = U} {U′ = U′}
    {vM =
      (left-syntax N.⟨ left-down-inert ⟩)
        N.⟨ left-up-inert ⟩}
    {vM′ =
      (right-syntax N.⟨ right-down-inert ⟩)
        N.⟨ right-up-inert ⟩}
    (quotient-up-aligned
      {A = A} {A′ = A′} {D = D} {D′ = D′}
      {u = u} {u′ = u′}
      (quotient-down-aligned
        {C = C} {C′ = C′} {D = D} {D′ = D′}
        {d = d} {d′ = d′}
        source-down target-down body D⊑E alignment)
      widening pA)
    runtime left-env right-env realization γ~γ′ supply
    left-final right-final
    | left-down-value , left-down , left-up-frame
    | right-down-value , right-down , right-up-frame
    with closed-value-inert-frame left-down
       | closed-value-inert-frame right-down
close-aligned-values
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {ρ = ρ} {γᵀ = γᵀ}
    {R = R} {γ = γ} {γ′ = γ′} {θ = θ} {θ′ = θ′}
    {U = U} {U′ = U′}
    {vM =
      (left-syntax N.⟨ left-down-inert ⟩)
        N.⟨ left-up-inert ⟩}
    {vM′ =
      (right-syntax N.⟨ right-down-inert ⟩)
        N.⟨ right-up-inert ⟩}
    (quotient-up-aligned
      {A = A} {A′ = A′} {D = D} {D′ = D′}
      {u = u} {u′ = u′}
      (quotient-down-aligned
        {C = C} {C′ = C′} {D = D} {D′ = D′}
        {d = d} {d′ = d′}
        source-down target-down body D⊑E alignment)
      widening pA)
    runtime left-env right-env realization γ~γ′ supply
    left-final right-final
    | left-down-value , left-down , left-up-frame
    | right-down-value , right-down , right-up-frame
    | left-value , left-base , left-down-frame
    | right-value , right-base , right-down-frame =
  quotient-value-frame⊑
    (quotient-value-frame
      {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      {ρ = ρ}
      {C = C} {C′ = C′} {D = D} {D′ = D′}
      {A = A} {A′ = A′}
      {d = d} {d′ = d′} {u = u} {u′ = u′}
      {θ = θ} {θ′ = θ′}
      {V = left-value} {V′ = right-value} {U = U} {U′ = U′}
      {id = left-down-inert} {id′ = right-down-inert}
      {iu = left-up-inert} {iu′ = right-up-inert}
      source-down target-down D⊑E alignment widening pA
      runtime
      left-down-frame right-down-frame
      left-up-frame right-up-frame)
    (closed-value-scoped
      (proj₁ (EnvironmentProof.environment-narrowing-scoped γ~γ′))
      (WorldProof.type-environment-left-scoped
        (environments-narrow realization))
      left-final)
    (closed-value-scoped
      (proj₂ (EnvironmentProof.environment-narrowing-scoped γ~γ′))
      (WorldProof.type-environment-right-scoped
        (environments-narrow realization))
      right-final)
    (close-aligned-values
      body runtime left-env right-env realization γ~γ′ supply
      left-base right-base)
close-aligned-values
    {ρ = ρ} {θ = θ} {θ′}
    (right-narrowing-cast-aligned
      {A = A} {A′} {B₁′} {B₂′} {p = p}
      seal cast body q)
    runtime left-env right-env realization γ~γ′ supply
    left-value
    (closed-function-proxy {p = p′} {q = q′} right-value) =
  right-function-proxy⊑
    (persistent-right-function-proxy
      {ρ = ρ} (right-narrowing-action
        {ρ = ρ} {A = A} {A′} {B′ = B₁′ ⇒ B₂′}
        {p = p} {q = q}
        cast-tag-or-id seal cast)
      runtime)
    (WorldProof.type-environment-right-scoped
      (environments-narrow realization))
    (close-aligned-values
      body runtime left-env right-env realization γ~γ′ supply
      left-value right-value)
close-aligned-values
    {ρ = ρ} {θ = θ} {θ′}
    (right-id-widening-cast-aligned
      {A = A} {A′} {B₁′} {B₂′} {p = p}
      seal cast body q)
    runtime left-env right-env realization γ~γ′ supply
    left-value
    (closed-function-proxy {p = p′} {q = q′} right-value) =
  right-function-proxy⊑
    (persistent-right-function-proxy
      {ρ = ρ}
      (right-static-widening-action
        {ρ = ρ} {A = A} {A′} {B′ = B₁′ ⇒ B₂′}
        {p = p} {q = q}
        seal cast)
      runtime)
    (WorldProof.type-environment-right-scoped
      (environments-narrow realization))
    (close-aligned-values
      body runtime left-env right-env realization γ~γ′ supply
      left-value right-value)

closeValue-preserves-narrowing :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ γᵀ M M′ A B p}
    {R : WorldRelation W W′}
    {γ γ′ θ θ′ U U′} →
  (terms :
    OpenInterpreterTermNarrowing
      R Φ Δᴸ Δᴿ ρ γᵀ M M′ A B p) →
  Frame.RuntimeFrameNarrowing R Φ Δᴸ Δᴿ ρ θ θ′ →
  EnvironmentTyping W θ γ (NTI.leftCtxⁱ γᵀ) →
  EnvironmentTyping W′ θ′ γ′ (NTI.rightCtxⁱ γᵀ) →
  TypeEnvironmentRealization R Φ θ θ′ →
  EnvironmentNarrowing R γ γ′ →
  nextAbstractIndex θ′ ≤ nextAbstractIndex θ →
  (vM : N.Value M) →
  (vM′ : N.Value M′) →
  closeValue vM γ θ ≡ just U →
  closeValue vM′ γ′ θ′ ≡ just U′ →
  ValueNarrowing R U U′
closeValue-preserves-narrowing
    {R = R}
    terms runtime left-env right-env realization γ~γ′ supply
    vM vM′ left-eq right-eq =
  close-aligned-values
    (term-alignment terms)
    runtime
    (λ R≤S S⊢ →
      SemanticProof.environment-weaken
        (Frame.left-world-extension R≤S) S⊢ left-env)
    (λ R≤S S⊢ →
      SemanticProof.environment-weaken
        (Frame.right-world-extension R≤S) S⊢ right-env)
    realization γ~γ′ supply
    (closeValue-closed vM left-eq)
    (closeValue-closed vM′ right-eq)

module proof.InterpreterCloseOperationalValueProof where

-- File Charter:
--   * Strengthens closing of aligned syntactic values with exact operational
--     producer certificates.
--   * Builds unary typing, structural value narrowing, and operational origin
--     in one structural traversal of the aligned value shape.
--   * Contains no interpreter call or reduction result.

import Data.List
open import Data.List using (_∷_)
import Data.Nat
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using
  (refl; subst; sym)

open import Interpreter
open import Runtime.InterpreterClosedValue
open import Runtime.InterpreterClosedValueFrame
open import Narrowing.InterpreterCoercionNarrowing using
  ( InterpreterTypeNarrowing
  ; operational-component
  ; right-static-widening-action
  ; right-narrowing-action
  )
open import Narrowing.InterpreterOperationalValueNarrowing
open import Narrowing.InterpreterEnvironmentNarrowing
open import Narrowing.InterpreterQuotientValueNarrowing using
  (quotient-value-frame)
open import Typing.InterpreterSemanticTypingCore
open import Simulation.Core.InterpreterSimulationContext
open import Narrowing.InterpreterTermNarrowing
open import Narrowing.InterpreterTypedValueNarrowing
open import Runtime.InterpreterTypeEnvironmentRealization
import Runtime.InterpreterRuntimeFrame
import Narrowing.InterpreterWorldNarrowing
import NuTermImprecision as NTI
import NuTerms as N
open import
  proof.NuImprecisionAssumptionMembershipUniquenessProof using
  ( assumption-membership-unique-matched
  ; assumption-membership-unique-source
  )
import Primitives
open import TermTyping using (cast-tag-or-id; forget)
open import Types
open import proof.InterpreterClosedValueStructural using
  (closed-value-instantiate-head)
open import proof.InterpreterCloseValueNarrowingProof using
  (close-aligned-values)
open import proof.InterpreterCloseValueTyping using
  (closedValue-typing)
open import proof.InterpreterClosingRuntimeFrame
open import proof.InterpreterOperationalEnvironmentLift
open import proof.InterpreterRuntimeFramePrefix using
  (runtime-frame-prefix)
import proof.InterpreterSemanticTypingProperties as SemanticProof

open InterpreterValues
open Narrowing.InterpreterTermNarrowing.RelatedWorlds

module EnvironmentProof =
  Narrowing.InterpreterEnvironmentNarrowing.EnvironmentNarrowing
    interpreterNarrowingLeaves

typed-closed-aligned :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ γᵀ M M′ A B p}
    {R : WorldRelation W W′}
    {γ γ′ θ θ′ U U′}
    {vM : N.Value M} {vM′ : N.Value M′} →
  AlignedInterpreterTermNarrowing
    Φ Δᴸ Δᴿ ρ γᵀ M M′ A B p →
  (runtime :
    RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (environment :
    EnvironmentRealization runtime γᵀ γ γ′) →
  ClosedValue γ θ vM U →
  ClosedValue γ′ θ′ vM′ U′ →
  TypedValueNarrowing ⟦ A ⟧[ θ ] ⟦ B ⟧[ θ′ ] R U U′
typed-closed-aligned
    {W = W} {W′ = W′}
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {ρ = ρ} {γᵀ = γᵀ}
    {M = M} {M′ = M′} {A = A} {B = B} {p = p}
    {R = R}
    alignment runtime environment
    left-closed right-closed =
  typed-value-narrowing
    (close-aligned-values
      alignment
      (runtime-narrowing-frame runtime)
      (λ R≤S S⊢ →
        SemanticProof.environment-weaken
          (Runtime.InterpreterRuntimeFrame.left-world-extension R≤S)
          S⊢ (left-environment-typed environment))
      (λ R≤S S′⊢ →
        SemanticProof.environment-weaken
          (Runtime.InterpreterRuntimeFrame.right-world-extension R≤S)
          S′⊢ (right-environment-typed environment))
      (type-environments-realized runtime)
      (environments-narrow environment)
      (abstract-supply runtime) left-closed right-closed)
    (left-world-typed runtime)
    (right-world-typed runtime)
    (closedValue-typing
      (left-world-typed runtime)
      (left-runtime-context runtime)
      (left-environment-typed environment)
      (interpreter-narrowing-source-term
        (aligned-term-shape alignment))
      (forget (open-interpreter-narrowing-source-typing
        {W = W} {W′ = W′}
        {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
        {ρ = ρ} {γ = γᵀ}
        {N = M} {N′ = M′} {A = A} {B = B} {p = p}
        {R = R}
        (open-interpreter-narrowing {R = R} alignment)))
      left-closed)
    (closedValue-typing
      (right-world-typed runtime)
      (right-runtime-context runtime)
      (right-environment-typed environment)
      (interpreter-narrowing-target-term
        (aligned-term-shape alignment))
      (forget (open-interpreter-narrowing-target-typing
        {W = W} {W′ = W′}
        {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
        {ρ = ρ} {γ = γᵀ}
        {N = M} {N′ = M′} {A = A} {B = B} {p = p}
        {R = R}
        (open-interpreter-narrowing {R = R} alignment)))
      right-closed)

close-aligned-operational :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ γᵀ M M′ A B p}
    {R : WorldRelation W W′}
    {γ γ′ θ θ′ U U′}
    {vM : N.Value M} {vM′ : N.Value M′} →
  (alignment :
    AlignedInterpreterTermNarrowing
      Φ Δᴸ Δᴿ ρ γᵀ M M′ A B p) →
  (runtime :
    RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (environment :
    EnvironmentRealization runtime γᵀ γ γ′) →
  OperationalEnvironmentNarrowing θ θ′ R γᵀ γ γ′ →
  ClosedValue γ θ vM U →
  ClosedValue γ′ θ′ vM′ U′ →
  OperationalValueNarrowing
    ⟦ A ⟧[ θ ] ⟦ B ⟧[ θ′ ] R U U′
close-aligned-operational
    (closure-aligned hA hA′ body)
    runtime environment origins
    closed-closure closed-closure =
  operational-value
    (typed-closed-aligned
      (closure-aligned hA hA′ body)
      runtime environment
      closed-closure closed-closure)
    (closure-origin runtime environment origins
      (open-interpreter-narrowing body))
close-aligned-operational
    {R = R} {γ = γ} {γ′} {θ} {θ′}
    {vM = N.Λ left-syntax} {vM′ = N.Λ right-syntax}
    alignment@(paired-type-abstraction-aligned
      {A = A-body} {B = B-body}
      store context vV vV′ termV termV′ body)
    runtime environment origins
    (closed-type-abstraction
      {U = V} {X = X} {vV = left-syntax}
      left-fresh left-body)
    (closed-type-abstraction
      {U = V′} {X = X′} {vV = right-syntax}
      right-fresh right-body) =
  operational-value
    (typed-closed-aligned alignment runtime environment
      (closed-type-abstraction
        left-fresh left-body)
      (closed-type-abstraction
        right-fresh right-body))
    (paired-type-abstraction-origin instantiate)
  where
  instantiate :
    ∀ {Z Z′ C C′ σ σ′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    (C~C′ : InterpreterTypeNarrowing C C′) →
    (σ~σ′ : TypeEnvironmentNarrowing S σ σ′) →
    WorldTyping (allocate Z C σ) →
    WorldTyping (allocate Z′ C′ σ′) →
    OperationalValueNarrowing
      (instantiateSemantic
        (nominal-type (seal-name (freshSealName Z)))
        (interpretType
          (bound-type Data.Nat.zero ∷
            Data.List.map liftSemantic (semanticEnvironment θ))
          A-body))
      (instantiateSemantic
        (nominal-type (seal-name (freshSealName Z′)))
        (interpretType
          (bound-type Data.Nat.zero ∷
            Data.List.map liftSemantic (semanticEnvironment θ′))
          B-body))
      (allocate-both S C~C′ σ~σ′)
      (substituteName X (freshSealName Z) V)
      (substituteName X′ (freshSealName Z′) V′)
  instantiate {Z = z} {Z′ = z′} R≤S C~C′ σ~σ′ Z⊢ Z′⊢ =
    operational-value-type-transport
      (sym (SemanticProof.instantiate-interpret
        (nominal-type (seal-name (freshSealName z)))
        θ A-body))
      (sym (SemanticProof.instantiate-interpret
        (nominal-type (seal-name (freshSealName z′)))
        θ′ B-body))
      (close-aligned-operational
        body
        allocated-runtime
        allocated-environment
        (paired-operational-environment-lift
          R≤S Z⊢ Z′⊢ context origins)
        (closed-value-instantiate-head left-fresh left-body)
        (closed-value-instantiate-head right-fresh right-body))
    where
    allocated-frame =
      paired-closing-runtime-frame
        (runtime-narrowing-frame runtime)
        R≤S C~C′ σ~σ′ store

    allocated-runtime =
      runtime-narrowing-from-frame Z⊢ Z′⊢
        (assumption-membership-unique-matched
          (assumption-membership-unique runtime))
        allocated-frame

    allocated-environment =
      environment-realization
        (EnvironmentProof.environment-narrowing-weaken
          (extension-both R≤S)
          (environments-narrow environment))
        (subst
          (EnvironmentTyping _
            (seal-name (freshSealName z) ∷ θ) γ)
          (sym (NTI.leftCtxⁱ-lift context))
          (SemanticProof.environment-type-weaken
            (seal-name (freshSealName z))
            (SemanticProof.environment-weaken
              (world-extension-allocate
                (Runtime.InterpreterRuntimeFrame.left-world-extension R≤S))
              Z⊢ (left-environment-typed environment))))
        (subst
          (EnvironmentTyping _
            (seal-name (freshSealName z′) ∷ θ′) γ′)
          (sym (NTI.rightCtxⁱ-lift context))
          (SemanticProof.environment-type-weaken
            (seal-name (freshSealName z′))
            (SemanticProof.environment-weaken
              (world-extension-allocate
                (Runtime.InterpreterRuntimeFrame.right-world-extension R≤S))
              Z′⊢ (right-environment-typed environment))))
close-aligned-operational
    {R = R} {γ = γ} {γ′} {θ} {θ′}
    {U′ = Q} {vM = N.Λ left-syntax}
    alignment@(left-type-abstraction-aligned
      {A = A-body} {B = B-target}
      occ store context vV termV termN′ body)
    runtime environment origins
    (closed-type-abstraction
      {U = V} {X = type-name X} {vV = left-syntax}
      left-fresh left-body)
    right-value =
  operational-value
    (typed-closed-aligned alignment runtime environment
      (closed-type-abstraction
        left-fresh left-body)
      right-value)
    (left-type-abstraction-origin instantiate)
  where
  instantiate :
    ∀ {Z Z′ C σ}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    (σ-ok : Narrowing.InterpreterWorldNarrowing.TypeEnvironmentScoped Z σ) →
    WorldTyping (allocate Z C σ) →
    WorldTyping Z′ →
    OperationalValueNarrowing
      (instantiateSemantic
        (nominal-type (seal-name (freshSealName Z)))
        (interpretType
          (bound-type Data.Nat.zero ∷
            Data.List.map liftSemantic (semanticEnvironment θ))
          A-body))
      ⟦ B-target ⟧[ θ′ ]
      (allocate-left-dynamic {A = C} S σ-ok)
      (substituteName (type-name X) (freshSealName Z) V)
      Q
  instantiate {Z = z} R≤S σ-ok Z⊢ Z′⊢ =
    operational-value-type-transport
      (sym (SemanticProof.instantiate-interpret
        (nominal-type (seal-name (freshSealName z)))
        θ A-body))
      refl
      (close-aligned-operational
        body
        allocated-runtime
        allocated-environment
        (left-operational-environment-lift
          R≤S Z⊢ Z′⊢ context origins)
        (closed-value-instantiate-head left-fresh left-body)
        right-value)
    where
    allocated-frame =
      left-closing-runtime-frame
        (runtime-narrowing-frame runtime)
        R≤S σ-ok store

    allocated-runtime =
      runtime-narrowing-from-frame Z⊢ Z′⊢
        (assumption-membership-unique-source
          (assumption-membership-unique runtime))
        allocated-frame

    allocated-environment =
      environment-realization
        (EnvironmentProof.environment-narrowing-weaken
          (extension-left R≤S)
          (environments-narrow environment))
        (subst
          (EnvironmentTyping _
            (seal-name (freshSealName z) ∷ θ) γ)
          (sym (NTI.leftCtxⁱ-lift-left context))
          (SemanticProof.environment-type-weaken
            (seal-name (freshSealName z))
            (SemanticProof.environment-weaken
              (world-extension-allocate
                (Runtime.InterpreterRuntimeFrame.left-world-extension R≤S))
              Z⊢ (left-environment-typed environment))))
        (subst
          (EnvironmentTyping _ θ′ γ′)
          (sym (NTI.rightCtxⁱ-lift-left context))
          (SemanticProof.environment-weaken
            (Runtime.InterpreterRuntimeFrame.right-world-extension R≤S)
            Z′⊢ (right-environment-typed environment)))
close-aligned-operational
    (allocation-prefix-aligned prefix body source target)
    runtime environment origins
    left-value right-value =
  close-aligned-operational
    body
    (runtime-narrowing-from-frame
      (left-world-typed runtime)
      (right-world-typed runtime)
      (assumption-membership-unique runtime)
      (runtime-frame-prefix prefix
        (runtime-narrowing-frame runtime)))
    (environment-realization
      (environments-narrow environment)
      (left-environment-typed environment)
      (right-environment-typed environment))
    origins left-value right-value
close-aligned-operational
    constant-aligned runtime environment origins
    (closed-constant (Primitives.κℕ n))
    (closed-constant .(Primitives.κℕ n)) =
  operational-value
    (typed-closed-aligned constant-aligned
      runtime environment
      (closed-constant (Primitives.κℕ n))
      (closed-constant (Primitives.κℕ n)))
    constant-origin
close-aligned-operational
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {ρ = ρ} {γᵀ = γᵀ}
    {R = R} {γ = γ} {γ′ = γ′} {θ = θ} {θ′ = θ′}
    {U = U} {U′ = U′}
    {vM =
      (left-syntax N.⟨ left-down-inert ⟩)
        N.⟨ left-up-inert ⟩}
    {vM′ =
      (right-syntax N.⟨ right-down-inert ⟩)
        N.⟨ right-up-inert ⟩}
    alignment@(quotient-up-aligned
      {A = A} {A′ = A′} {D = D} {D′ = D′}
      {u = u} {u′ = u′}
      quotient@(quotient-down-aligned
        {C = C} {C′ = C′} {D = D} {D′ = D′}
        {d = d} {d′ = d′}
        source-down target-down body D⊑E route)
      widening pA)
    runtime environment origins
    left-final right-final
    with closed-value-inert-frame left-final
       | closed-value-inert-frame right-final
close-aligned-operational
    alignment@(quotient-up-aligned
      quotient@(quotient-down-aligned
        source-down target-down body D⊑E route)
      widening pA)
    runtime environment origins
    left-final right-final
    | left-down-value , left-down , left-up-frame
    | right-down-value , right-down , right-up-frame
    with closed-value-inert-frame left-down
       | closed-value-inert-frame right-down
close-aligned-operational
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {ρ = ρ} {γᵀ = γᵀ}
    {R = R} {γ = γ} {γ′ = γ′} {θ = θ} {θ′ = θ′}
    {U = U} {U′ = U′}
    {vM =
      (left-syntax N.⟨ left-down-inert ⟩)
        N.⟨ left-up-inert ⟩}
    {vM′ =
      (right-syntax N.⟨ right-down-inert ⟩)
        N.⟨ right-up-inert ⟩}
    alignment@(quotient-up-aligned
      {A = A} {A′ = A′} {D = D} {D′ = D′}
      {u = u} {u′ = u′}
      quotient@(quotient-down-aligned
        {C = C} {C′ = C′} {D = D} {D′ = D′}
        {d = d} {d′ = d′}
        source-down target-down body D⊑E route)
      widening pA)
    runtime environment origins
    left-final right-final
    | left-down-value , left-down , left-up-frame
    | right-down-value , right-down , right-up-frame
    | left-value , left-base , left-down-frame
    | right-value , right-base , right-down-frame =
  operational-value
    (typed-closed-aligned alignment runtime environment
      left-final right-final)
    (quotient-origin
      runtime
      (open-interpreter-narrowing body)
      (open-interpreter-narrowing alignment)
      refl refl
      frame
      (close-aligned-operational
        body runtime environment origins
        left-base right-base))
  where
  frame =
    quotient-value-frame
      {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      {ρ = ρ}
      {C = C} {C′ = C′} {D = D} {D′ = D′}
      {A = A} {A′ = A′}
      {d = d} {d′ = d′} {u = u} {u′ = u′}
      {θ = θ} {θ′ = θ′}
      {V = left-value} {V′ = right-value}
      {U = U} {U′ = U′}
      {id = left-down-inert} {id′ = right-down-inert}
      {iu = left-up-inert} {iu′ = right-up-inert}
      source-down target-down D⊑E route widening pA
      (runtime-narrowing-frame runtime)
      left-down-frame right-down-frame
      left-up-frame right-up-frame
close-aligned-operational
    {ρ = ρ}
    alignment@(right-narrowing-cast-aligned
      {A = A} {A′ = A′} {B₁′} {B₂′} {p = p}
      seal cast body q)
    runtime environment origins
    left-value
    (closed-function-proxy right-value) =
  operational-value
    (typed-closed-aligned alignment runtime environment
      left-value (closed-function-proxy right-value))
    (right-function-boundary-origin runtime
      (operational-component
        (right-narrowing-action
        {ρ = ρ} {A = A} {A′ = A′}
        {B′ = B₁′ ⇒ B₂′} {p = p} {q = q}
        cast-tag-or-id seal cast))
      (close-aligned-operational
        body runtime environment origins
        left-value right-value)
      refl)
close-aligned-operational
    {ρ = ρ}
    alignment@(right-id-widening-cast-aligned
      {A = A} {A′ = A′} {B₁′} {B₂′} {p = p}
      seal cast body q)
    runtime environment origins
    left-value
    (closed-function-proxy right-value) =
  operational-value
    (typed-closed-aligned alignment runtime environment
      left-value (closed-function-proxy right-value))
    (right-function-boundary-origin runtime
      (operational-component
        (right-static-widening-action
        {ρ = ρ} {A = A} {A′ = A′}
        {B′ = B₁′ ⇒ B₂′} {p = p} {q = q}
        seal cast))
      (close-aligned-operational
        body runtime environment origins
        left-value right-value)
      refl)

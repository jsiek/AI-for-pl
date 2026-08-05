module proof.InterpreterCloseFramedValueProof where

-- File Charter:
--   * Closes compiler-aligned syntactic values into the exact framed value
--     relation used by the mutual interpreter proof.
--   * Builds future paired and source-only allocation certificates while
--     retaining exact static precision indices.
--   * Contains no interpreter execution, reduction, or catch-up result.

open import Agda.Builtin.Equality using (refl)
open import Data.List using (_∷_)
import Data.Nat
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import ImprecisionWf using
  (_ˣ⊑★; _ˣ⊑ˣ_; ⇑ᵢ; ⇑ᴸᵢ)
open import Interpreter
open import Runtime.InterpreterClosedValue
open import Runtime.InterpreterClosedValueFrame
open import Narrowing.InterpreterCoercionNarrowing using
  ( InterpreterTypeNarrowing
  ; operational-component
  ; right-static-widening-action
  ; right-narrowing-action
  )
open import Narrowing.InterpreterEnvironmentNarrowing
open import Simulation.Framed.InterpreterFramedEnvironmentLift
open import Narrowing.InterpreterFramedValueNarrowing
open import Narrowing.InterpreterFramedValueNarrowingProperties
open import Narrowing.InterpreterOperationalCoercionNarrowing using
  (operational-coercion-prefix)
open import Narrowing.InterpreterQuotientValueNarrowing using
  (quotient-value-frame)
open import Typing.InterpreterSemanticTypingCore
open import Simulation.Core.InterpreterSimulationContext
open import Narrowing.InterpreterTermNarrowing
open import Runtime.InterpreterTypeEnvironmentRealization
import Runtime.InterpreterRuntimeFrame
import Narrowing.InterpreterWorldNarrowing
import NuTermImprecision as NTI
import NuTerms as N
open import NarrowWiden using (narrow-weaken)
import Primitives
open import TermTyping using (cast-tag-or-id; forget)
open import QuotientedTermImprecision using
  (StoreImpPrefix; prefix-reflⁱ)
open import proof.InterpreterAlignedTermPrefix using
  (aligned-term-prefix-weaken)
open import proof.InterpreterClosedValueStructural using
  (closed-value-instantiate-head)
import proof.InterpreterCoercionNarrowingProof as CoercionProof
open import proof.InterpreterCloseOperationalValueProof using
  (close-aligned-operational; typed-closed-aligned)
open import proof.NuImprecisionStorePrefix using
  ( leftStoreⁱ-prefix-inclusion
  ; rightStoreⁱ-prefix-inclusion
  ; store-imp-prefix-transⁱ
  )
open import proof.NuImprecisionStorePrefixLiftLemma using
  (left-store-prefix-liftᵀ; paired-store-prefix-liftᵀ)
import proof.InterpreterSemanticTypingProperties as SemanticProof
open import
  proof.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import
  proof.NuImprecisionAssumptionMembershipUniquenessProof using
  ( assumption-membership-unique-matched
  ; assumption-membership-unique-source
  )
open import Types

open Narrowing.InterpreterTermNarrowing.InterpreterValues
open Narrowing.InterpreterTermNarrowing.RelatedWorlds

module EnvironmentProof =
  Narrowing.InterpreterEnvironmentNarrowing.EnvironmentNarrowing
    interpreterNarrowingLeaves

close-aligned-framed-under-prefix :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ₀ ρ γᵀ M M′ A B p}
    {R : WorldRelation W W′}
    {γ γ′ θ θ′ U U′}
    {vM : N.Value M} {vM′ : N.Value M′} →
  AssumptionMembershipUnique Φ →
  StoreImpPrefix ρ₀ ρ →
  (alignment :
    AlignedInterpreterTermNarrowing
      Φ Δᴸ Δᴿ ρ₀ γᵀ M M′ A B p) →
  (runtime :
    RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (environment :
    EnvironmentRealization runtime γᵀ γ γ′) →
  FramedEnvironmentNarrowing runtime γᵀ γ γ′ →
  ClosedValue γ θ vM U →
  ClosedValue γ′ θ′ vM′ U′ →
  FramedValueNarrowing
    {A = A} {A′ = B} {p = p} runtime U U′
close-aligned-framed-under-prefix unique prefix
    alignment@(closure-aligned hA hA′ body)
    runtime environment origins
    closed-closure closed-closure =
  framed-value
    (typed-closed-aligned ambient-alignment runtime environment
      closed-closure closed-closure)
    (close-aligned-operational ambient-alignment runtime environment
      (framed-environment-operational origins)
      closed-closure closed-closure)
    (closure-originᶠ environment origins
      (open-interpreter-narrowing
        (aligned-term-prefix-weaken prefix body)))
  where
  ambient-alignment =
    aligned-term-prefix-weaken prefix alignment
close-aligned-framed-under-prefix
    {Φ = Φ} {R = R} {γ = γ} {γ′} {θ} {θ′}
    {vM = N.Λ left-syntax} {vM′ = N.Λ right-syntax}
    unique prefix
    alignment@(paired-type-abstraction-aligned
      {ρ′ = ρ′} {A = A-body} {B = B-body}
      {p = p-body}
      store context vV vV′ termV termV′ body)
    runtime environment origins
    (closed-type-abstraction
      {U = V} {X = X} {vV = left-syntax}
      left-fresh left-body)
    (closed-type-abstraction
      {U = V′} {X = X′} {vV = right-syntax}
      right-fresh right-body)
    with paired-store-prefix-liftᵀ prefix store
close-aligned-framed-under-prefix
    {Φ = Φ} {R = R} {γ = γ} {γ′} {θ} {θ′}
    {vM = N.Λ left-syntax} {vM′ = N.Λ right-syntax}
    unique prefix
    alignment@(paired-type-abstraction-aligned
      {A = A-body} {B = B-body} {p = p-body}
      store context vV vV′ termV termV′ body)
    runtime environment origins
    (closed-type-abstraction
      {U = V} {X = X} {vV = left-syntax}
      left-fresh left-body)
    (closed-type-abstraction
      {U = V′} {X = X′} {vV = right-syntax}
      right-fresh right-body)
    | ambient-store , ambient-lift , lifted-prefix =
  framed-value
    (typed-closed-aligned ambient-alignment runtime environment
      (closed-type-abstraction left-fresh left-body)
      (closed-type-abstraction right-fresh right-body))
    (close-aligned-operational ambient-alignment runtime environment
      (framed-environment-operational origins)
      (closed-type-abstraction left-fresh left-body)
      (closed-type-abstraction right-fresh right-body))
    (paired-type-abstraction-originᶠ
      {ρ′ = ambient-store} {A = A-body}
      {A′ = B-body} {p = p-body}
      ambient-lift instantiate)
  where
  ambient-alignment =
    aligned-term-prefix-weaken prefix alignment

  instantiate :
    ∀ {U U′ C C′ σ σ′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    (C~C′ : InterpreterTypeNarrowing C C′) →
    (σ~σ′ : TypeEnvironmentNarrowing S σ σ′) →
    (allocated :
      RuntimeNarrowing
        (allocate-both S C~C′ σ~σ′)
        ((Data.Nat.zero ˣ⊑ˣ Data.Nat.zero) ∷ ⇑ᵢ Φ)
        _ _
        ambient-store
        (seal-name (freshSealName U) ∷ θ)
        (seal-name (freshSealName U′) ∷ θ′)) →
    FramedValueNarrowing
      {A = A-body} {A′ = B-body} {p = p-body} allocated
      (substituteName X (freshSealName U) V)
      (substituteName X′ (freshSealName U′) V′)
  instantiate {U = U} {U′} R≤S C~C′ σ~σ′ allocated =
    close-aligned-framed-under-prefix
      (assumption-membership-unique-matched unique)
      lifted-prefix body allocated allocated-environment
      (paired-framed-environment-lift
        unique (extension-both R≤S) context origins)
      (closed-value-instantiate-head left-fresh left-body)
      (closed-value-instantiate-head right-fresh right-body)
    where
    allocated-environment =
      environment-realization
        (EnvironmentProof.environment-narrowing-weaken
          (extension-both R≤S)
          (environments-narrow environment))
        (subst
          (EnvironmentTyping _
            (seal-name (freshSealName U) ∷ θ) γ)
          (sym (NTI.leftCtxⁱ-lift context))
          (SemanticProof.environment-type-weaken
            (seal-name (freshSealName U))
            (SemanticProof.environment-weaken
              (world-extension-allocate
                (Runtime.InterpreterRuntimeFrame.left-world-extension R≤S))
              (left-world-typed allocated)
              (left-environment-typed environment))))
        (subst
          (EnvironmentTyping _
            (seal-name (freshSealName U′) ∷ θ′) γ′)
          (sym (NTI.rightCtxⁱ-lift context))
          (SemanticProof.environment-type-weaken
            (seal-name (freshSealName U′))
            (SemanticProof.environment-weaken
              (world-extension-allocate
                (Runtime.InterpreterRuntimeFrame.right-world-extension R≤S))
              (right-world-typed allocated)
              (right-environment-typed environment))))
close-aligned-framed-under-prefix
    {Φ = Φ} {R = R} {γ = γ} {γ′} {θ} {θ′}
    {U′ = Q} {vM = N.Λ left-syntax}
    unique prefix
    alignment@(left-type-abstraction-aligned
      {ρ′ = ρ′} {A = A-body} {B = B-target}
      {p = p-body}
      occ store context vV termV termN′ body)
    runtime environment origins
    (closed-type-abstraction
      {U = V} {X = type-name X} {vV = left-syntax}
      left-fresh left-body)
    right-value
    with left-store-prefix-liftᵀ prefix store
close-aligned-framed-under-prefix
    {Φ = Φ} {R = R} {γ = γ} {γ′} {θ} {θ′}
    {U′ = Q} {vM = N.Λ left-syntax}
    unique prefix
    alignment@(left-type-abstraction-aligned
      {A = A-body} {B = B-target} {p = p-body}
      occ store context vV termV termN′ body)
    runtime environment origins
    (closed-type-abstraction
      {U = V} {X = type-name X} {vV = left-syntax}
      left-fresh left-body)
    right-value
    | ambient-store , ambient-lift , lifted-prefix =
  framed-value
    (typed-closed-aligned ambient-alignment runtime environment
      (closed-type-abstraction left-fresh left-body)
      right-value)
    (close-aligned-operational ambient-alignment runtime environment
      (framed-environment-operational origins)
      (closed-type-abstraction left-fresh left-body)
      right-value)
    (left-type-abstraction-originᶠ
      {ρ′ = ambient-store} {A = A-body}
      {T = B-target} {p = p-body}
      ambient-lift instantiate)
  where
  ambient-alignment =
    aligned-term-prefix-weaken prefix alignment

  instantiate :
    ∀ {U U′ C σ}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    (σ-ok : Narrowing.InterpreterWorldNarrowing.TypeEnvironmentScoped U σ) →
    (allocated :
      RuntimeNarrowing
        (allocate-left-dynamic {A = C} S σ-ok)
        ((Data.Nat.zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        _ _
        ambient-store
        (seal-name (freshSealName U) ∷ θ) θ′) →
    FramedValueNarrowing
      {A = A-body} {A′ = B-target} {p = p-body} allocated
      (substituteName (type-name X) (freshSealName U) V) Q
  instantiate {U = U} R≤S σ-ok allocated =
    close-aligned-framed-under-prefix
      (assumption-membership-unique-source unique)
      lifted-prefix body allocated allocated-environment
      (left-framed-environment-lift
        unique (extension-left R≤S) context origins)
      (closed-value-instantiate-head left-fresh left-body)
      right-value
    where
    allocated-environment =
      environment-realization
        (EnvironmentProof.environment-narrowing-weaken
          (extension-left R≤S)
          (environments-narrow environment))
        (subst
          (EnvironmentTyping _
            (seal-name (freshSealName U) ∷ θ) γ)
          (sym (NTI.leftCtxⁱ-lift-left context))
          (SemanticProof.environment-type-weaken
            (seal-name (freshSealName U))
            (SemanticProof.environment-weaken
              (world-extension-allocate
                (Runtime.InterpreterRuntimeFrame.left-world-extension R≤S))
              (left-world-typed allocated)
              (left-environment-typed environment))))
        (subst
          (EnvironmentTyping _ θ′ γ′)
          (sym (NTI.rightCtxⁱ-lift-left context))
          (SemanticProof.environment-weaken
            (Runtime.InterpreterRuntimeFrame.right-world-extension R≤S)
            (right-world-typed allocated)
            (right-environment-typed environment)))
close-aligned-framed-under-prefix unique prefix
    (allocation-prefix-aligned prefix₀ body source target)
    runtime environment origins left-value right-value =
  close-aligned-framed-under-prefix unique
    (store-imp-prefix-transⁱ prefix₀ prefix)
    body runtime environment origins left-value right-value
close-aligned-framed-under-prefix unique prefix constant-aligned
    runtime environment origins
    (closed-constant (Primitives.κℕ n))
    (closed-constant .(Primitives.κℕ n)) =
  framed-value
    (typed-closed-aligned
      (aligned-term-prefix-weaken prefix constant-aligned)
      runtime environment
      (closed-constant (Primitives.κℕ n))
      (closed-constant (Primitives.κℕ n)))
    (close-aligned-operational
      (aligned-term-prefix-weaken prefix constant-aligned)
      runtime environment
      (framed-environment-operational origins)
      (closed-constant (Primitives.κℕ n))
      (closed-constant (Primitives.κℕ n)))
    constant-originᶠ
close-aligned-framed-under-prefix
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {ρ = ρ} {γᵀ = γᵀ}
    {R = R} {θ = θ} {θ′ = θ′}
    {U = U} {U′ = U′}
    {vM =
      (left-syntax N.⟨ left-down-inert ⟩)
        N.⟨ left-up-inert ⟩}
    {vM′ =
      (right-syntax N.⟨ right-down-inert ⟩)
        N.⟨ right-up-inert ⟩}
    unique prefix
    alignment@(quotient-up-aligned
      {A = A} {A′ = A′} {D = D} {D′ = D′}
      {u = u} {u′ = u′}
      quotient@(quotient-down-aligned
        {C = C} {C′ = C′}
        {d = d} {d′ = d′}
        source-down target-down body D⊑E route)
      widening pA)
    runtime environment origins left-final right-final
    with closed-value-inert-frame left-final
       | closed-value-inert-frame right-final
close-aligned-framed-under-prefix unique prefix
    alignment@(quotient-up-aligned
      quotient@(quotient-down-aligned
        source-down target-down body D⊑E route)
      widening pA)
    runtime environment origins left-final right-final
    | left-down-value , left-down , left-up-frame
    | right-down-value , right-down , right-up-frame
    with closed-value-inert-frame left-down
       | closed-value-inert-frame right-down
close-aligned-framed-under-prefix
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
    unique prefix
    alignment@(quotient-up-aligned
      {A = A} {A′ = A′} {D = D} {D′ = D′}
      {u = u} {u′ = u′}
      quotient@(quotient-down-aligned
        {C = C} {C′ = C′} {D = D} {D′ = D′}
        {d = d} {d′ = d′}
        source-down target-down body D⊑E route)
      widening pA)
    runtime environment origins left-final right-final
    | left-down-value , left-down , left-up-frame
    | right-down-value , right-down , right-up-frame
    | left-value , left-base , left-down-frame
    | right-value , right-base , right-down-frame =
  framed-value
    (typed-closed-aligned ambient-alignment runtime environment
      left-final right-final)
    (close-aligned-operational ambient-alignment runtime environment
      (framed-environment-operational origins)
      left-final right-final)
    (quotient-originᶠ
      (open-interpreter-narrowing ambient-body)
      (open-interpreter-narrowing ambient-alignment)
      frame
      (close-aligned-framed-under-prefix
        unique prefix body runtime environment
        origins left-base right-base))
  where
  ambient-body =
    aligned-term-prefix-weaken prefix body

  ambient-source-down =
    narrow-weaken ≤-refl
      (leftStoreⁱ-prefix-inclusion prefix)
      source-down

  ambient-target-down =
    narrow-weaken ≤-refl
      (rightStoreⁱ-prefix-inclusion prefix)
      target-down

  ambient-widening =
    CoercionProof.quotient-widening-prefix prefix widening

  ambient-alignment =
    quotient-up-aligned
      (quotient-down-aligned
        ambient-source-down ambient-target-down
        ambient-body D⊑E route)
      ambient-widening pA

  frame =
    quotient-value-frame
      ambient-source-down ambient-target-down
      D⊑E route ambient-widening pA
      (runtime-narrowing-frame runtime)
      left-down-frame right-down-frame
      left-up-frame right-up-frame
close-aligned-framed-under-prefix
    {ρ = ρ}
    unique prefix
    alignment@(right-narrowing-cast-aligned
      {A = A} {A′ = A′} {B₁′} {B₂′} {p = p}
      seal cast body q)
    runtime environment origins
    left-value (closed-function-proxy right-value) =
  operationally-framed-value
    (close-aligned-operational ambient-alignment runtime environment
      (framed-environment-operational origins)
      left-value (closed-function-proxy right-value))
  where
  ambient-alignment =
    aligned-term-prefix-weaken prefix alignment
close-aligned-framed-under-prefix
    {ρ = ρ}
    unique prefix
    alignment@(right-id-widening-cast-aligned
      {A = A} {A′ = A′} {B₁′} {B₂′} {p = p}
      seal cast body q)
    runtime environment origins
    left-value (closed-function-proxy right-value) =
  operationally-framed-value
    (close-aligned-operational ambient-alignment runtime environment
      (framed-environment-operational origins)
      left-value (closed-function-proxy right-value))
  where
  ambient-alignment =
    aligned-term-prefix-weaken prefix alignment

close-aligned-framed :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ γᵀ M M′ A B p}
    {R : WorldRelation W W′}
    {γ γ′ θ θ′ U U′}
    {vM : N.Value M} {vM′ : N.Value M′} →
  AssumptionMembershipUnique Φ →
  (alignment :
    AlignedInterpreterTermNarrowing
      Φ Δᴸ Δᴿ ρ γᵀ M M′ A B p) →
  (runtime :
    RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (environment :
    EnvironmentRealization runtime γᵀ γ γ′) →
  FramedEnvironmentNarrowing runtime γᵀ γ γ′ →
  ClosedValue γ θ vM U →
  ClosedValue γ′ θ′ vM′ U′ →
  FramedValueNarrowing
    {A = A} {A′ = B} {p = p} runtime U U′
close-aligned-framed unique alignment =
  close-aligned-framed-under-prefix
    unique prefix-reflⁱ alignment

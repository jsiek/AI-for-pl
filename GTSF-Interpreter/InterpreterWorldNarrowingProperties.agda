module InterpreterWorldNarrowingProperties where

-- File Charter:
--   * Exposes the main structural theorems for interpreter world narrowing.
--   * Keeps proof recursion private in
--     `proof.InterpreterWorldNarrowingProof`.
--   * Contains no reduction-dependent result.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (_×_; Σ-syntax)

open import Interpreter
open import InterpreterWorldNarrowing
import proof.InterpreterWorldNarrowingProof as Proof
import proof.InterpreterWorldScopeProof as ScopeProof
open import Types

module WorldNarrowingProperties
  (TypeNarrowing : Ty → Ty → Set₁)
  where

  open WorldNarrowing TypeNarrowing
  module Implementation = Proof.WorldNarrowingProof TypeNarrowing
  module ScopeImplementation = ScopeProof.WorldScopeProof TypeNarrowing

  seal-link-functional :
    ∀ {W W′ α α′ β′} {R : WorldRelation W W′} →
    SealLink R α α′ →
    SealLink R α β′ →
    α′ ≡ β′
  seal-link-functional =
    Implementation.seal-link-functional

  seal-link-injective :
    ∀ {W W′ α β α′} {R : WorldRelation W W′} →
    SealLink R α α′ →
    SealLink R β α′ →
    α ≡ β
  seal-link-injective =
    Implementation.seal-link-injective

  seal-link-left-allocated :
    ∀ {W W′ α α′} {R : WorldRelation W W′} →
    SealLink R α α′ →
    Allocated W α
  seal-link-left-allocated =
    Implementation.seal-link-left-allocated

  seal-link-right-allocated :
    ∀ {W W′ α α′} {R : WorldRelation W W′} →
    SealLink R α α′ →
    Allocated W′ α′
  seal-link-right-allocated =
    Implementation.seal-link-right-allocated

  type-environment-left-scoped :
    ∀ {W W′ θ θ′} {R : WorldRelation W W′} →
    TypeEnvironmentNarrowing R θ θ′ →
    TypeEnvironmentScoped W θ
  type-environment-left-scoped =
    ScopeImplementation.type-environment-left-scoped

  type-environment-right-scoped :
    ∀ {W W′ θ θ′} {R : WorldRelation W W′} →
    TypeEnvironmentNarrowing R θ θ′ →
    TypeEnvironmentScoped W′ θ′
  type-environment-right-scoped =
    ScopeImplementation.type-environment-right-scoped

  world-extension-trans :
    ∀ {W W′ U U′ Z Z′}
      {R : WorldRelation W W′}
      {S : WorldRelation U U′}
      {T : WorldRelation Z Z′} →
    WorldExtension R S →
    WorldExtension S T →
    WorldExtension R T
  world-extension-trans =
    Implementation.world-extension-trans

  seal-link-weaken :
    ∀ {W W′ U U′ α α′}
      {R : WorldRelation W W′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    SealLink R α α′ →
    SealLink S α α′
  seal-link-weaken =
    Implementation.seal-link-weaken

  type-environment-narrowing-weaken :
    ∀ {W W′ U U′ θ θ′}
      {R : WorldRelation W W′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    TypeEnvironmentNarrowing R θ θ′ →
    TypeEnvironmentNarrowing S θ θ′
  type-environment-narrowing-weaken =
    Implementation.type-environment-narrowing-weaken

  type-environment-left-scope-weaken :
    ∀ {W W′ U U′ θ}
      {R : WorldRelation W W′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    TypeEnvironmentScoped W θ →
    TypeEnvironmentScoped U θ
  type-environment-left-scope-weaken =
    ScopeImplementation.type-environment-left-scope-weaken

  type-environment-right-scope-weaken :
    ∀ {W W′ U U′ θ′}
      {R : WorldRelation W W′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    TypeEnvironmentScoped W′ θ′ →
    TypeEnvironmentScoped U′ θ′
  type-environment-right-scope-weaken =
    ScopeImplementation.type-environment-right-scope-weaken

  seal-link-respects-allocations :
    ∀ {W W′ α α′} {R : WorldRelation W W′} →
    SealLink R α α′ →
    Σ[ A ∈ Ty ]
    Σ[ θ ∈ TypeEnvironment ]
    Σ[ A′ ∈ Ty ]
    Σ[ θ′ ∈ TypeEnvironment ]
      allocation α A θ ∈ allocations W ×
      allocation α′ A′ θ′ ∈ allocations W′ ×
      TypeNarrowing A A′ ×
      TypeEnvironmentNarrowing R θ θ′
  seal-link-respects-allocations =
    Implementation.seal-link-respects-allocations

module proof.InterpreterLeftTypeAbstractionNarrowingProof where

-- File Charter:
--   * Eliminates the source-only abstraction certificate at a future world.
--   * Retains the actual allocation type and allocation scope.
--   * Contains no interpreter execution or reduction argument.

open import Interpreter
open import Narrowing.InterpreterValueNarrowing
open import Narrowing.InterpreterWorldNarrowing

module LeftTypeAbstractionNarrowingProof
  (leaves : NarrowingLeaves)
  where

  module Values = ValueNarrowing leaves
  open Values
  open Values.RelatedWorlds

  instantiate-related-left-type-abstraction :
    ∀ {W W′ U U′ A σ X V V′}
      {R : WorldRelation W W′}
      {S : WorldRelation U U′} →
    LeftTypeAbstractionNarrowing R X V V′ →
    WorldExtension R S →
    (σ-ok : TypeEnvironmentScoped U σ) →
    ValueNarrowing
      (allocate-left-dynamic {A = A} S σ-ok)
      (substituteName X (freshSealName U) V)
      V′
  instantiate-related-left-type-abstraction
      abstraction R≤S σ-ok =
    instantiate-left-body abstraction R≤S σ-ok

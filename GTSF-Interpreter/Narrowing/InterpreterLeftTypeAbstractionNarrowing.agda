module Narrowing.InterpreterLeftTypeAbstractionNarrowing where

-- File Charter:
--   * Public elimination of source-only type-abstraction narrowing.
--   * Instantiates the source binder at an arbitrary future left allocation.
--   * Delegates certificate elimination to a reduction-free proof module.

open import Interpreter
open import Narrowing.InterpreterValueNarrowing
open import Narrowing.InterpreterWorldNarrowing
import proof.InterpreterLeftTypeAbstractionNarrowingProof as Proof

module LeftTypeAbstractionNarrowing
  (leaves : NarrowingLeaves)
  where

  module Values = ValueNarrowing leaves
  open Values
  open Values.RelatedWorlds

  module Implementation =
    Proof.LeftTypeAbstractionNarrowingProof leaves

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
  instantiate-related-left-type-abstraction =
    Implementation.instantiate-related-left-type-abstraction

module Narrowing.InterpreterTypeAbstractionNarrowing where

-- File Charter:
--   * Exposes direct paired instantiation for alpha-aware semantic type
--     abstractions.
--   * Allows the two stored binder names to differ and allocates a related
--     fresh nominal seal on each side.
--   * Delegates the certificate elimination to a private proof module.

open import Interpreter
open import Narrowing.InterpreterValueNarrowing
open import Narrowing.InterpreterWorldNarrowing
import proof.InterpreterTypeAbstractionNarrowingProof as Proof

module TypeAbstractionNarrowing
  (leaves : NarrowingLeaves)
  where

  module Values = ValueNarrowing leaves
  open Values
  open Values.RelatedWorlds

  module Implementation =
    Proof.TypeAbstractionNarrowingProof leaves

  instantiate-related-type-abstraction :
    ∀ {W W′ A A′ θ θ′ X X′ V V′}
      {R : WorldRelation W W′} →
    TypeAbstractionNarrowing R X X′ V V′ →
    (A~A′ : TypeNarrowing leaves A A′) →
    (θ~θ′ : TypeEnvironmentNarrowing R θ θ′) →
    ValueNarrowing
      (allocate-both R A~A′ θ~θ′)
      (substituteName X (freshSealName W) V)
      (substituteName X′ (freshSealName W′) V′)
  instantiate-related-type-abstraction =
    Implementation.instantiate-related-type-abstraction

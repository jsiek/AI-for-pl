module proof.InterpreterTypeAbstractionNarrowingProof where

-- File Charter:
--   * Eliminates an alpha-aware type-abstraction certificate at the current
--     related worlds.
--   * Substitutes the two possibly different binders with the freshly paired
--     nominal seals allocated by the interpreter.
--   * Contains no evaluator, small-step, or reduction-derived argument.

open import Interpreter
open import Narrowing.InterpreterValueNarrowing
open import Narrowing.InterpreterWorldNarrowing

module TypeAbstractionNarrowingProof
  (leaves : NarrowingLeaves)
  where

  module Values = ValueNarrowing leaves
  open Values
  open Values.RelatedWorlds

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
  instantiate-related-type-abstraction abstraction A~A′ θ~θ′ =
    instantiate-bodies abstraction extension-refl A~A′ θ~θ′

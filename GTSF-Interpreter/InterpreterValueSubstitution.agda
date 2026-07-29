module InterpreterValueSubstitution where

-- File Charter:
--   * Exposes paired fresh-name substitution for narrowed semantic values.
--   * States the theorem directly at the interpreter-value interface.
--   * Delegates the exhaustive value proof to a private module.

open import Interpreter
open import InterpreterValueNarrowing
open import InterpreterWorldNarrowing
import proof.InterpreterValueSubstitutionProof as Proof

module ValueSubstitution
  (leaves : NarrowingLeaves)
  where

  module Values = ValueNarrowing leaves
  open Values
  open Values.RelatedWorlds

  module Implementation = Proof.ValueSubstitutionProof leaves

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
  substitute-name-preserves-value-narrowing =
    Implementation.substitute-name-preserves-value-narrowing

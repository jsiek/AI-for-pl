module Narrowing.InterpreterTypedValueNarrowingProperties where

-- File Charter:
--   * Public weakening theorem for typed value narrowing.
--   * States the required final-world typing witnesses explicitly.
--   * Delegates its proof to the focused reduction-free proof module.

open import Typing.InterpreterSemanticTypingCore
open import Narrowing.InterpreterTermNarrowing
open import Narrowing.InterpreterTypedValueNarrowing
import proof.InterpreterTypedValueNarrowingProof as Proof

open Narrowing.InterpreterTermNarrowing.RelatedWorlds

typed-value-narrowing-weaken :
  ∀ {W W′ U U′ A B V V′}
    {R : WorldRelation W W′}
    {S : WorldRelation U U′} →
  Narrowing.InterpreterTermNarrowing.RelatedWorlds.WorldExtension R S →
  WorldTyping U →
  WorldTyping U′ →
  TypedValueNarrowing A B R V V′ →
  TypedValueNarrowing A B S V V′
typed-value-narrowing-weaken =
  Proof.typed-value-narrowing-weaken

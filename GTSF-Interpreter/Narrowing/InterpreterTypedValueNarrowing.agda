module Narrowing.InterpreterTypedValueNarrowing where

-- File Charter:
--   * Strengthens semantic value narrowing with unary semantic typing for
--     both returned endpoints.
--   * Supplies the type-indexed result relation used by recursive interpreter
--     simulation.
--   * Erases directly to the world-indexed value relation used by DGG.

open import Interpreter using (Value; World)
open import Typing.InterpreterSemanticTypingCore using
  (SemanticType; ValueTyping; WorldTyping)
open import Simulation.Core.InterpreterSimulationResult using
  (ValueResultRelation)
import Narrowing.InterpreterTermNarrowing as ITN

open ITN.InterpreterValues
open ITN.RelatedWorlds

record TypedValueNarrowing
    (A B : SemanticType)
    {W W′ : World}
    (R : WorldRelation W W′)
    (V V′ : Value) : Set₁ where
  constructor typed-value-narrowing
  field
    values-narrow :
      ValueNarrowing R V V′

    left-world-typed :
      WorldTyping W

    right-world-typed :
      WorldTyping W′

    left-value-typed :
      ValueTyping W V A

    right-value-typed :
      ValueTyping W′ V′ B

open TypedValueNarrowing public

TypedValueResult :
  SemanticType →
  SemanticType →
  ValueResultRelation
TypedValueResult A B R V V′ =
  TypedValueNarrowing A B R V V′

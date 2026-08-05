module proof.InterpreterOperationalNameInstantiationProof where

-- File Charter:
--   * Transports an exact operational value origin when one source abstract
--     name is replaced by an allocated nominal seal.
--   * Keeps the original operational origin available to later observers.
--   * Contains no interpreter call, reduction, or catch-up theorem.

open import Agda.Builtin.Equality using (_≡_)

open import Interpreter
open import Narrowing.InterpreterOperationalValueNarrowing
open import Typing.InterpreterSemanticTypingCore using (SemanticType)
open import Narrowing.InterpreterTermNarrowing
open import Narrowing.InterpreterTypedValueNarrowing using (TypedValueNarrowing)
open import Narrowing.InterpreterWorldNarrowing using (Allocated)

open Narrowing.InterpreterTermNarrowing.RelatedWorlds


left-name-instantiated-operational :
  ∀ {W W′ U U′ A B C X α V V′ L}
    {R : WorldRelation W W′}
    {S : WorldRelation U U′} →
  TypedValueNarrowing C B S L V′ →
  Narrowing.InterpreterTermNarrowing.RelatedWorlds.WorldExtension R S →
  Allocated U α →
  substituteName X α V ≡ L →
  OperationalValueNarrowing A B R V V′ →
  OperationalValueNarrowing C B S L V′
left-name-instantiated-operational
    typed R≤S α-ok result-eq value =
  operational-value typed
    (left-name-instantiated-origin R≤S α-ok result-eq value)

module Runtime.InterpreterOperationalNameInstantiation where

-- File Charter:
--   * Exposes exact operational origin transport from an abstract source
--     name to a freshly allocated nominal seal.
--   * States the full typed conclusion at the use site.
--   * Delegates its reduction-free proof to a focused private module.

open import Agda.Builtin.Equality using (_≡_)

open import Interpreter
open import Narrowing.InterpreterOperationalValueNarrowing
open import Typing.InterpreterSemanticTypingCore using (SemanticType)
open import Narrowing.InterpreterTermNarrowing
open import Narrowing.InterpreterTypedValueNarrowing using (TypedValueNarrowing)
open import Narrowing.InterpreterWorldNarrowing using (Allocated)
import proof.InterpreterOperationalNameInstantiationProof as Proof

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
left-name-instantiated-operational =
  Proof.left-name-instantiated-operational

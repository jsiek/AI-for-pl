module proof.InterpreterTypeEnvironmentRealizationPropertiesProof where

-- File Charter:
--   * Proves source-dynamic seal lookup inversion.
--   * Separates abstract binder names from dynamically allocated seals.
--   * Contains no interpreter computation or reduction semantics.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (sym; trans)

open import ImprecisionWf using (_ˣ⊑★)
open import Interpreter
open import Runtime.InterpreterTypeEnvironmentRealization

open RelatedWorlds

source-dynamic-seal-lookup :
  ∀ {W W′ θ θ′ X α}
    {R : WorldRelation W W′} →
  AssumptionRealization R θ θ′ (X ˣ⊑★) →
  lookup θ X ≡ just (seal-name α) →
  LeftDynamicSeal R α
source-dynamic-seal-lookup
    (source-dynamic-assumption left-at source-dynamic-abstract)
    lookup-eq
    with trans (sym left-at) lookup-eq
source-dynamic-seal-lookup
    (source-dynamic-assumption left-at source-dynamic-abstract)
    lookup-eq
    | ()
source-dynamic-seal-lookup
    (source-dynamic-assumption left-at
      (source-dynamic-seal dynamic))
    lookup-eq
    with trans (sym left-at) lookup-eq
source-dynamic-seal-lookup
    (source-dynamic-assumption left-at
      (source-dynamic-seal dynamic))
    lookup-eq
    | refl =
  dynamic

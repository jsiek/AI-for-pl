module proof.InterpreterTypeAbstractionInstantiationHelpers where

-- File Charter:
--   * Supplies direct computation and semantic-typing facts for
--     type-abstraction instantiation.
--   * Is shared by paired and source-only simulation leaves.
--   * Uses no narrowing, small-step, or reduction-derived theorem.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (zero; suc)

open import Interpreter
open import Typing.InterpreterInstantiationSemanticTyping
open import Typing.InterpreterSemanticTyping
open import Simulation.Core.InterpreterSimulationResult using (immediateReturn)
open import Narrowing.InterpreterWorldNarrowing using (allocated)

type-abstraction-instantiation-computation :
  ∀ {W α X V} n →
  instantiateValue W α (type-abstraction X V) n ≡
  immediateReturn W (substituteName X α V) n
type-abstraction-instantiation-computation zero =
  refl
type-abstraction-instantiation-computation (suc n) =
  refl

instantiated-type-abstraction-typing :
  ∀ {W A θ body X V} →
  WorldTyping (allocate W A θ) →
  ValueTyping W (type-abstraction X V)
    (polymorphic-type body) →
  ValueTyping
    (allocate W A θ)
    (substituteName X (freshSealName W) V)
    (instantiateSemantic
      (nominal-type (seal-name (freshSealName W))) body)
instantiated-type-abstraction-typing
    {W} {A} {θ} {body} {X} {V}
    allocated-W⊢ V⊢
    with instantiateValue-preserves-semantic-typing
      (suc zero)
      allocated-W⊢
      (allocated (here refl))
      (semantic-value-world-weaken
        (world-extension-allocate world-extension-refl)
        allocated-W⊢ V⊢)
instantiated-type-abstraction-typing
    allocated-W⊢ V⊢
    | return-typed W≤U U⊢ result-typed =
  result-typed

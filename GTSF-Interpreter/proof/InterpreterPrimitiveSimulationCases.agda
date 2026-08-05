module proof.InterpreterPrimitiveSimulationCases where

-- File Charter:
--   * Proves direct simulation of the interpreter's natural-number primitive.
--   * Uses semantic canonical forms to exclude the raw expected-natural error.
--   * Contains no term, coercion, or reduction case analysis.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat using (_+_)
open import Data.Product using (_,_; Σ-syntax)

open import Interpreter
import Narrowing.InterpreterQuotientValueNarrowing as IQVN
open import Typing.InterpreterSemanticTypingCore
open import Simulation.Core.InterpreterSimulationResult
open import Narrowing.InterpreterTypedValueNarrowing
open import Runtime.InterpreterValueSubstitutionShape using
  (substitute-name-constant-source)
import Narrowing.InterpreterTermNarrowing as ITN
open import Primitives using (addℕ; κℕ)
open import proof.InterpreterSimulationHelpers using
  (fixed-return-simulation)
open import Types using (`ℕ)

open ITN.InterpreterValues
open ITN.RelatedWorlds

natural-value-canonical :
  ∀ {W V} →
  ValueTyping W V (base-type `ℕ) →
  Σ[ n ∈ StepIndex ] V ≡ constant (κℕ n)
natural-value-canonical constant-typed =
  _ , refl

constant-narrowing-injective :
  ∀ {W W′ κ κ′}
    {R : WorldRelation W W′} →
  ValueNarrowing R (constant κ) (constant κ′) →
  κ ≡ κ′
constant-narrowing-injective (constant⊑ κ) =
  refl
constant-narrowing-injective
    (quotient-value-frame⊑
      (IQVN.quotient-value-frame
        source-down target-down D⊑E alignment widening pA
        realization left-down right-down () right-up)
      left-scoped right-scoped base-narrowing)
constant-narrowing-injective
    (quotient-value-frame⊑
      (IQVN.quotient-down-value-frame
        source-down target-down D⊑E alignment realization
        () right-final)
      left-scoped right-scoped base-narrowing)
constant-narrowing-injective {κ = κ}
    (left-name-instantiated⊑
      {X = X} {α = α} {V = V}
      R≤S α-ok result-eq base-narrowing)
    with substitute-name-constant-source X α V result-eq
constant-narrowing-injective {κ = κ}
    (left-name-instantiated⊑
      {X = X} {α = α} {V = .(constant κ)}
      R≤S α-ok result-eq base-narrowing)
    | refl =
  constant-narrowing-injective base-narrowing

primitive-simulation :
  ∀ {W W′ V V′ U U′}
    {R : WorldRelation W W′} →
  ValueNarrowing R V V′ →
  ValueNarrowing R U U′ →
  ValueTyping W V (base-type `ℕ) →
  ValueTyping W′ V′ (base-type `ℕ) →
  ValueTyping W U (base-type `ℕ) →
  ValueTyping W′ U′ (base-type `ℕ) →
  TerminalSimulation ValueNarrowing R
    (fixedOutcome (applyPrimitive W addℕ V U))
    (fixedOutcome (applyPrimitive W′ addℕ V′ U′))
primitive-simulation V~V′ U~U′ V⊢ V′⊢ U⊢ U′⊢
    with natural-value-canonical V⊢
       | natural-value-canonical V′⊢
       | natural-value-canonical U⊢
       | natural-value-canonical U′⊢
primitive-simulation V~V′ U~U′ V⊢ V′⊢ U⊢ U′⊢
    | m , refl | m′ , refl | n , refl | n′ , refl
    with constant-narrowing-injective V~V′
       | constant-narrowing-injective U~U′
primitive-simulation V~V′ U~U′ V⊢ V′⊢ U⊢ U′⊢
    | m , refl | .m , refl | n , refl | .n , refl
    | refl | refl =
  fixed-return-simulation (constant⊑ (κℕ (m + n)))

typed-primitive-simulation :
  ∀ {W W′ V V′ U U′}
    {R : WorldRelation W W′} →
  TypedValueNarrowing
    (base-type `ℕ) (base-type `ℕ) R V V′ →
  TypedValueNarrowing
    (base-type `ℕ) (base-type `ℕ) R U U′ →
  TerminalSimulation
    (TypedValueResult (base-type `ℕ) (base-type `ℕ))
    R
    (fixedOutcome (applyPrimitive W addℕ V U))
    (fixedOutcome (applyPrimitive W′ addℕ V′ U′))
typed-primitive-simulation
    (typed-value-narrowing V~V′ W⊢ W′⊢ V⊢ V′⊢)
    (typed-value-narrowing U~U′ W⊢′ W′⊢′ U⊢ U′⊢)
    with natural-value-canonical V⊢
       | natural-value-canonical V′⊢
       | natural-value-canonical U⊢
       | natural-value-canonical U′⊢
typed-primitive-simulation
    (typed-value-narrowing V~V′ W⊢ W′⊢ V⊢ V′⊢)
    (typed-value-narrowing U~U′ W⊢′ W′⊢′ U⊢ U′⊢)
    | m , refl | m′ , refl | n , refl | n′ , refl
    with constant-narrowing-injective V~V′
       | constant-narrowing-injective U~U′
typed-primitive-simulation
    (typed-value-narrowing V~V′ W⊢ W′⊢ V⊢ V′⊢)
    (typed-value-narrowing U~U′ W⊢′ W′⊢′ U⊢ U′⊢)
    | m , refl | .m , refl | n , refl | .n , refl
    | refl | refl =
  fixed-return-simulation
    (typed-value-narrowing
      (constant⊑ (κℕ (m + n)))
      W⊢
      W′⊢
      constant-typed
      constant-typed)

module proof.InterpreterFramedSealCoercionProof where

-- File Charter:
--   * Proves the exact paired seal simulation.
--   * Constructs returned typing from unary coercion typing and records the
--     original framed value immediately below each new sealed wrapper.
--   * Contains no recursive interpreter, reduction, or catch-up result.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Coercions using (cast-seal)
open import Coercions renaming (seal to sealᶜ)
open import Conversion using
  (conceal-seal)
import Data.Maybe
open import Data.Nat using (suc; zero)
open import Data.Product using (_,_)
open import ImprecisionWf using
  (_∣_⊢_⊑_⊣_)
open import Interpreter
open import Simulation.Coercion.InterpreterCoercionComponents using
  (component-left-applied-typing; component-right-applied-typing)
open import Narrowing.InterpreterCoercionNarrowing
open import Typing.InterpreterCoercionSemanticTyping
open import Narrowing.InterpreterFramedValueNarrowing
open import Narrowing.InterpreterFramedValueNarrowingProperties using
  ( framed-value-operational
  ; framed-value-typed
  ; typed-value-type-transport
  )
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Narrowing.InterpreterOperationalValueNarrowing
open import Narrowing.InterpreterReachableCoercionNarrowing
open import Typing.InterpreterSemanticTypingCore
open import Typing.InterpreterSemanticTyping using
  (semantic-type-name-lookup; store-environment-lookup)
open import Simulation.Core.InterpreterSimulationContext
open import Simulation.Core.InterpreterSimulationResult using (immediateReturn)
open import Runtime.InterpreterStoreCorrespondenceRealization using
  (realizes-store-correspondence)
open import Narrowing.InterpreterTermNarrowing
open import Narrowing.InterpreterTypedValueNarrowing
open import Runtime.InterpreterTypeEnvironmentRealization using
  (realizes-assumption)
open import Runtime.InterpreterTypeEnvironmentRealizationProperties using
  (source-dynamic-seal-lookup)
open import Narrowing.InterpreterValueNarrowing using
  (NotSealed; tagged-not-sealed)
open import NarrowWiden using (sealⁿ)
import NuTermImprecision as NTI
import QuotientedTermImprecision as QTI
open import proof.InterpreterIndexedSimulationTransport using
  (indexed-simulation-pointwise)
open import proof.InterpreterOperationalEnvironmentLift using
  (operational-value-type-transport)
open import proof.InterpreterSimulationHelpers using
  (immediate-return-simulation)
open import proof.InterpreterTypedSimulationProof using
  (returned-value-typing)
open import Relation.Binary.PropositionalEquality using (sym)
open import Types

open Narrowing.InterpreterTermNarrowing.InterpreterValues
open Narrowing.InterpreterTermNarrowing.RelatedWorlds


coerce-seal-computation :
  ∀ {W θ C X V α} →
  lookup θ X ≡ Data.Maybe.just (seal-name α) →
  ∀ n →
  coerceValue W θ (sealᶜ C X) V n ≡
    immediateReturn W (sealed α V) n
coerce-seal-computation lookup-eq zero =
  refl
coerce-seal-computation lookup-eq (suc n)
    rewrite lookup-eq =
  refl


dynamic-value-not-sealed :
  ∀ {W V} →
  ValueTyping W V dynamic-type →
  NotSealed V
dynamic-value-not-sealed
    (tagged-typed W⊢ runtime runtime-ground environment cast V⊢) =
  tagged-not-sealed


indexed-framed-paired-seal :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ ρ θ θ′
      A A′ C D X Y p q V V′}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (action :
    ReachableComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
      (apply-coercion (sealᶜ C X))
      (apply-coercion (sealᶜ D Y))
      {A} {A′} {＇ X} {＇ Y} p q) →
  FramedValueNarrowing
    {A = A} {A′ = A′} {p = p} runtime V V′ →
  IndexedTerminalSimulation
    (FramedValueResult ρ θ θ′ q) R
    (coerceValue W θ (sealᶜ C X) V)
    (coerceValue W′ θ′ (sealᶜ D Y) V′)
    (suc left-index) (suc right-index)
indexed-framed-paired-seal
    runtime
    action@(reachable-paired-conversion
      (QTI.paired-conceal corresponds
        (conceal-seal hC X∈Σ allowed)
        (conceal-seal hD Y∈Σ allowed′)))
    value
    with realizes-store-correspondence
      (store-correspondences-realized runtime) corresponds
indexed-framed-paired-seal
    {left-index} {right-index}
    {W} {W′} {θ = θ} {θ′}
    {C = C} {D} {X} {Y} {V = V} {V′}
    runtime
    action@(reachable-paired-conversion
      (QTI.paired-conceal corresponds
        (conceal-seal hC X∈Σ allowed)
        (conceal-seal hD Y∈Σ allowed′)))
    value
    | α , α′ , left-eq , right-eq , α~α′ =
  indexed-simulation-pointwise
    (coerce-seal-computation
      {W = W} {θ} {C} {X} {V} {α} left-eq)
    (coerce-seal-computation
      {W = W′} {θ = θ′} {C = D} {X = Y}
      {V = V′} {α = α′} right-eq)
    (terminal-simulation-index
      (immediate-return-simulation
        (framed-result runtime
          (framed-value output-typed output-operational
            (paired-seal-originᶠ
              (reachable-component action) value)))))
  where
  input = framed-value-typed value

  left-action = reachable-component action
  left-typing = component-left-applied-typing left-action
  right-typing = component-right-applied-typing left-action

  output-typed =
    typed-value-narrowing
      (sealed⊑ α~α′ (values-narrow input))
      (left-world-typed input)
      (right-world-typed input)
      (returned-value-typing
        (coerceValue-preserves-semantic-typing
          (suc zero) (left-world-typed input)
          (left-runtime-context runtime)
          (Data.Product.proj₂ left-typing)
          (left-value-typed input))
        (coerce-seal-computation
          {W = W} {θ} {C} {X} {V} {α}
          left-eq (suc zero)))
      (returned-value-typing
        (coerceValue-preserves-semantic-typing
          (suc zero) (right-world-typed input)
          (right-runtime-context runtime)
          (Data.Product.proj₂ right-typing)
          (right-value-typed input))
        (coerce-seal-computation
          {W = W′} {θ = θ′} {C = D} {X = Y}
          {V = V′} {α = α′} right-eq (suc zero)))

  left-semantics =
    semantic-type-name-lookup
      {θ = θ} {X = X} {name = seal-name α} left-eq
  right-semantics =
    semantic-type-name-lookup
      {θ = θ′} {X = Y} {name = seal-name α′} right-eq

  output-typed-nominal =
    typed-value-type-transport
      left-semantics right-semantics output-typed

  output-operational =
    operational-value-type-transport
      (sym left-semantics) (sym right-semantics)
      (operational-value output-typed-nominal
        (paired-seal-origin runtime (reachable-component action)
          (framed-value-operational value)))

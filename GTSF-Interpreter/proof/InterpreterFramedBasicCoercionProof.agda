module proof.InterpreterFramedBasicCoercionProof where

-- File Charter:
--   * EXPERIMENTAL (O34): the tag proof predates the distinction between
--     suspended abstract environments and executable all-seal environments.
--   * Proves exact identity and tag simulations from direct equations.
--   * Uses static ground evidence and unary typing for returned tags.
--   * Contains no recursive interpreter or reduction result.

open import Agda.Builtin.Equality using (refl)
open import Coercions renaming (id to idᶜ; _! to _!ᶜ)
open import Data.Nat using (suc; zero)
open import Data.Product using (_,_)
open import ImprecisionWf using
  (_∣_⊢_⊑_⊣_; ⊑-src-wf; ⊑-tgt-wf)
open import Interpreter
open import Simulation.Coercion.InterpreterCoercionComponents
open import Simulation.Coercion.InterpreterCoercionComputation
open import Narrowing.InterpreterCoercionNarrowing
open import Typing.InterpreterCoercionSemanticTyping
open import Narrowing.InterpreterFramedValueNarrowing
open import Narrowing.InterpreterFramedValueNarrowingProperties using
  (framed-value-operational; framed-value-typed)
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Narrowing.InterpreterOperationalValueNarrowing
open import Typing.InterpreterSemanticTypingCore
open import Simulation.Core.InterpreterSimulationContext
open import Simulation.Core.InterpreterSimulationResult using (immediateReturn)
open import Narrowing.InterpreterTagNarrowing
open import Narrowing.InterpreterTermNarrowing
open import Narrowing.InterpreterTypedValueNarrowing
import Runtime.InterpreterTypeEnvironmentRealization as TER
import Narrowing.InterpreterWorldNarrowingProperties as WorldNarrowing
import NuTermImprecision as NTI
open import proof.InterpreterCoercionTyping using
  (ground?-complete; tagOf-complete)
open import proof.InterpreterIndexedSimulationTransport using
  (indexed-simulation-pointwise)
open import proof.InterpreterSimulationHelpers using
  (immediate-return-simulation)
open import proof.InterpreterTypedSimulationProof using
  (returned-value-typing)
open import Types

open Narrowing.InterpreterTermNarrowing.InterpreterValues
open Narrowing.InterpreterTermNarrowing.RelatedWorlds

module WorldProperties =
  WorldNarrowing.WorldNarrowingProperties InterpreterTypeNarrowing

indexed-framed-paired-id :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ ρ θ θ′
      A A′ p q V V′}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  FramedValueNarrowing
    {A = A} {A′ = A′} {p = p} runtime V V′ →
  IndexedTerminalSimulation
    (FramedValueResult ρ θ θ′ q) R
    (coerceValue W θ (idᶜ A) V)
    (coerceValue W′ θ′ (idᶜ A′) V′)
    (suc left-index) (suc right-index)
indexed-framed-paired-id runtime value =
  indexed-simulation-pointwise
    coerce-id-computation coerce-id-computation
    (terminal-simulation-index
      (immediate-return-simulation
        (framed-result runtime
          (reindexed-value (framed-value-typed value) value))))

indexed-framed-left-id :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ ρ θ θ′
      A A′ p q V V′}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  FramedValueNarrowing
    {A = A} {A′ = A′} {p = p} runtime V V′ →
  IndexedTerminalSimulation
    (FramedValueResult ρ θ θ′ q) R
    (coerceValue W θ (idᶜ A) V)
    (immediateReturn W′ V′)
    (suc left-index) right-index
indexed-framed-left-id runtime value =
  indexed-simulation-pointwise
    coerce-id-computation (λ n → refl)
    (terminal-simulation-index
      (immediate-return-simulation
        (framed-result runtime
          (reindexed-value (framed-value-typed value) value))))

indexed-framed-right-id :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ ρ θ θ′
      A A′ p q V V′}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  FramedValueNarrowing
    {A = A} {A′ = A′} {p = p} runtime V V′ →
  IndexedTerminalSimulation
    (FramedValueResult ρ θ θ′ q) R
    (immediateReturn W V)
    (coerceValue W′ θ′ (idᶜ A′) V′)
    left-index (suc right-index)
indexed-framed-right-id runtime value =
  indexed-simulation-pointwise
    (λ n → refl) coerce-id-computation
    (terminal-simulation-index
      (immediate-return-simulation
        (framed-result runtime
          (reindexed-value (framed-value-typed value) value))))

indexed-framed-paired-tag :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ ρ θ θ′
      A A′ G H p q V V′}
    {gG : Ground G} {gH : Ground H}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (action :
    ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
      (apply-coercion (G !ᶜ)) (apply-coercion (H !ᶜ))
      {A} {A′} {★} {★} p q) →
  FramedValueNarrowing
    {A = A} {A′ = A′} {p = p} runtime V V′ →
  IndexedTerminalSimulation
    (FramedValueResult ρ θ θ′ q) R
    (coerceValue W θ (G !ᶜ) V)
    (coerceValue W′ θ′ (H !ᶜ) V′)
    (suc left-index) (suc right-index)
indexed-framed-paired-tag
    {p = p} {q = ImprecisionWf.id★}
    {gG = gG} {gH} runtime action value
    with ground?-complete gG | ground?-complete gH
       | component-left-applied-typing action
       | component-right-applied-typing action
indexed-framed-paired-tag
    {left-index} {right-index}
    {p = p} {q = ImprecisionWf.id★}
    {gG = gG} {gH} runtime action value
    | gG′ , ground-eq | gH′ , ground-eq′
    | μ , left-typing@(cast-tag hG source-ground allowed)
    | μ′ , right-typing@(cast-tag hH target-ground allowed′)
    with tagOf-complete (left-runtime-context runtime)
           hG gG′
       | tagOf-complete (right-runtime-context runtime)
           hH gH′
indexed-framed-paired-tag
    {left-index} {right-index}
    {p = p} {q = ImprecisionWf.id★}
    {gG = gG} {gH} runtime action value
    | gG′ , ground-eq | gH′ , ground-eq′
    | μ , left-typing@(cast-tag hG source-ground allowed)
    | μ′ , right-typing@(cast-tag hH target-ground allowed′)
    | tag , tag-eq | tag′ , tag-eq′ =
  indexed-simulation-pointwise
    (coerce-tag-computation ground-eq tag-eq)
    (coerce-tag-computation ground-eq′ tag-eq′)
    (terminal-simulation-index
      (immediate-return-simulation
        (framed-result runtime
          (framed-value output-typed output-operational
            (paired-tag-originᶠ action value)))))
  where
  input = framed-value-typed value

  output-typed =
    typed-value-narrowing
      (tagged⊑
        (ground-narrowing (type-narrowing p))
        (TER.environments-narrow
          (type-environments-realized runtime))
        (values-narrow input))
      (left-world-typed input)
      (right-world-typed input)
      (returned-value-typing
        (coerceValue-preserves-semantic-typing
          (suc zero) (left-world-typed input)
          (left-runtime-context runtime) left-typing
          (left-value-typed input))
        (coerce-tag-computation ground-eq tag-eq (suc zero)))
      (returned-value-typing
        (coerceValue-preserves-semantic-typing
          (suc zero) (right-world-typed input)
          (right-runtime-context runtime) right-typing
          (right-value-typed input))
        (coerce-tag-computation ground-eq′ tag-eq′ (suc zero)))

  output-operational =
    operational-value output-typed
      (paired-tag-origin runtime action
        (framed-value-operational value))

indexed-framed-left-tag :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ ρ θ θ′
      A G p q V V′}
    {gG : Ground G}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (action :
    ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
      (apply-coercion (G !ᶜ)) skip-coercion
      {A} {★} {★} {★} p q) →
  FramedValueNarrowing
    {A = A} {A′ = ★} {p = p} runtime V V′ →
  IndexedTerminalSimulation
    (FramedValueResult ρ θ θ′ q) R
    (coerceValue W θ (G !ᶜ) V)
    (immediateReturn W′ V′)
    (suc left-index) right-index
indexed-framed-left-tag
    {p = p} {q = ImprecisionWf.id★}
    {gG = gG} runtime action value
    with ground?-complete gG
       | component-left-applied-typing action
indexed-framed-left-tag
    {left-index} {right-index}
    {p = p} {q = ImprecisionWf.id★}
    {gG = gG} runtime action value
    | gG′ , ground-eq
    | μ , left-typing@(cast-tag hG source-ground allowed)
    with tagOf-complete (left-runtime-context runtime)
      hG gG′
indexed-framed-left-tag
    {left-index} {right-index}
    {p = p} {q = ImprecisionWf.id★}
    {gG = gG} runtime action value
    | gG′ , ground-eq
    | μ , left-typing@(cast-tag hG source-ground allowed)
    | tag , tag-eq =
  indexed-simulation-pointwise
    (coerce-tag-computation ground-eq tag-eq)
    (λ n → refl)
    (terminal-simulation-index
      (immediate-return-simulation
        (framed-result runtime
          (framed-value output-typed output-operational
            (left-tag-originᶠ action value)))))
  where
  input = framed-value-typed value

  output-typed =
    typed-value-narrowing
      (left-tagged⊑
        (type-narrowing p)
        (WorldProperties.type-environment-left-scoped
          (TER.environments-narrow
            (type-environments-realized runtime)))
        (values-narrow input))
      (left-world-typed input)
      (right-world-typed input)
      (returned-value-typing
        (coerceValue-preserves-semantic-typing
          (suc zero) (left-world-typed input)
          (left-runtime-context runtime) left-typing
          (left-value-typed input))
        (coerce-tag-computation ground-eq tag-eq (suc zero)))
      (right-value-typed input)

  output-operational =
    operational-value output-typed
      (left-tag-origin runtime action
        (framed-value-operational value))

indexed-framed-right-tag :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ ρ θ θ′
      A′ H p q V V′}
    {gH : Ground H}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (action :
    ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
      skip-coercion (apply-coercion (H !ᶜ))
      {★} {A′} {★} {★} p q) →
  FramedValueNarrowing
    {A = ★} {A′ = A′} {p = p} runtime V V′ →
  IndexedTerminalSimulation
    (FramedValueResult ρ θ θ′ q) R
    (immediateReturn W V)
    (coerceValue W′ θ′ (H !ᶜ) V′)
    left-index (suc right-index)
indexed-framed-right-tag
    {p = p} {q = ImprecisionWf.id★}
    {gH = gH} runtime action value
    with ground?-complete gH
       | component-right-applied-typing action
indexed-framed-right-tag
    {left-index} {right-index}
    {p = p} {q = ImprecisionWf.id★}
    {gH = gH} runtime action value
    | gH′ , ground-eq
    | μ′ , right-typing@(cast-tag hH target-ground allowed′)
    with tagOf-complete (right-runtime-context runtime)
      hH gH′
indexed-framed-right-tag
    {left-index} {right-index}
    {p = p} {q = ImprecisionWf.id★}
    {gH = gH} runtime action value
    | gH′ , ground-eq
    | μ′ , right-typing@(cast-tag hH target-ground allowed′)
    | tag′ , tag-eq′ =
  indexed-simulation-pointwise
    (λ n → refl)
    (coerce-tag-computation ground-eq tag-eq′)
    (terminal-simulation-index
      (immediate-return-simulation
        (framed-result runtime
          (framed-value output-typed output-operational
            (right-tag-originᶠ action value)))))
  where
  input = framed-value-typed value

  output-typed =
    typed-value-narrowing
      (right-tagged⊑
        (type-narrowing p)
        (WorldProperties.type-environment-right-scoped
          (TER.environments-narrow
            (type-environments-realized runtime)))
        (values-narrow input))
      (left-world-typed input)
      (right-world-typed input)
      (left-value-typed input)
      (returned-value-typing
        (coerceValue-preserves-semantic-typing
          (suc zero) (right-world-typed input)
          (right-runtime-context runtime) right-typing
          (right-value-typed input))
        (coerce-tag-computation ground-eq tag-eq′ (suc zero)))

  output-operational =
    operational-value output-typed
      (right-tag-origin runtime action
        (framed-value-operational value))

module proof.InterpreterOperationalQuotientImmediateProof where

-- File Charter:
--   * Executes paired inert quotient downcasts into the operational
--     quotient intermediate at arbitrary positive observation indices.
--   * Constructs the exact returned-value frames and direct equations.
--   * Contains no recursion, small-step reduction, or catch-up theorem.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Coercions using (Coercion; Inert)
open import Data.Nat using (suc; zero)
open import Data.Product using (proj₁; proj₂)

open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import Interpreter
open import Runtime.InterpreterClosedValueFrame
open import Simulation.Coercion.InterpreterCoercionComponents
open import Narrowing.InterpreterCoercionNarrowing
open import Typing.InterpreterCoercionSemanticTyping
open import Narrowing.InterpreterFramedValueNarrowing
open import Narrowing.InterpreterFramedValueNarrowingProperties using
  (framed-value-operational; framed-value-typed)
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Runtime.InterpreterInertFrame
open import Narrowing.InterpreterOperationalValueNarrowing
open import Narrowing.InterpreterOperationalQuotientValueNarrowing
open import Narrowing.InterpreterQuotientValueNarrowing
open import Typing.InterpreterSemanticTyping using (semantic-value-scoped)
open import Simulation.Core.InterpreterSimulationContext
open import Narrowing.InterpreterTermNarrowing
open import Narrowing.InterpreterTypedValueNarrowing
open import Narrowing.InterpreterValueNarrowing
import NuTermImprecision as NTI
import QuotientedTermImprecision as QTI
open import proof.EndpointCanonicalMLBSimpleQuotient using
  ( EndpointRepresentativeAlignment
  ; endpoint-representatives-quotient
  )
open import proof.InterpreterIndexedImmediateReturn using
  (indexed-immediate-returns)
open import proof.InterpreterTypedSimulationProof using
  (returned-value-typing)
open import Types

open Narrowing.InterpreterTermNarrowing.InterpreterValues
open Narrowing.InterpreterTermNarrowing.RelatedWorlds

indexed-quotient-down-inert :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {θ θ′ C C′ D D′ X Y E d d′ V V′}
    {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
    {D⊑E : Φ ∣ Δᴸ ⊢ D ⊑ E ⊣ Δᴿ}
    {alignment : EndpointRepresentativeAlignment Δᴿ X Y E D′}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (down :
    OperationalDownCoercionNarrowing
      Φ Δᴸ Δᴿ ρ d d′ pC
      (endpoint-representatives-quotient D⊑E alignment)) →
  (left-inert : Inert d) →
  (right-inert : Inert d′) →
  (value :
    FramedValueNarrowing
      {A = C} {A′ = C′} {p = pC} runtime V V′) →
  IndexedTerminalSimulation
    (OperationalQuotientValueNarrowing
      runtime d d′ D⊑E alignment down)
    R
    (coerceValue W θ d V)
    (coerceValue W′ θ′ d′ V′)
    (suc left-index) (suc right-index)
indexed-quotient-down-inert
    runtime
    down@(paired-id-down-action source target)
    left-inert right-inert value
    with execute-inert-frame
      (left-runtime-context runtime) (proj₁ source) left-inert
       | execute-inert-frame
      (right-runtime-context runtime) (proj₁ target) right-inert
indexed-quotient-down-inert
    {left-index} {right-index}
    runtime
    down@(paired-id-down-action source target)
    left-inert right-inert value
    | inert-frame-execution L left-frame left-eq
    | inert-frame-execution L′ right-frame right-eq =
  indexed-immediate-returns
    (left-eq left-index)
    (right-eq right-index)
    (left-eq zero)
    (right-eq zero)
    (quotient-down-inert-return
      value left-frame right-frame
      left-eq right-eq)
indexed-quotient-down-inert
    runtime
    down@(paired-generalized-down-action source target)
    left-inert right-inert value
    with execute-inert-frame
      (left-runtime-context runtime) (proj₁ source) left-inert
       | execute-inert-frame
      (right-runtime-context runtime) (proj₁ target) right-inert
indexed-quotient-down-inert
    {left-index} {right-index}
    runtime
    down@(paired-generalized-down-action source target)
    left-inert right-inert value
    | inert-frame-execution L left-frame left-eq
    | inert-frame-execution L′ right-frame right-eq =
  indexed-immediate-returns
    (left-eq left-index)
    (right-eq right-index)
    (left-eq zero)
    (right-eq zero)
    (quotient-down-inert-return
      value left-frame right-frame
      left-eq right-eq)

indexed-quotient-up-inert :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {θ θ′ C C′ D D′ A A′ X Y E d d′ u u′}
    {V V′ L L′ : Value}
    {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
    {D⊑E : Φ ∣ Δᴸ ⊢ D ⊑ E ⊣ Δᴿ}
    {alignment : EndpointRepresentativeAlignment Δᴿ X Y E D′}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {R : WorldRelation W W′}
    {left-down-inert : Inert d}
    {right-down-inert : Inert d′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (down :
    OperationalDownCoercionNarrowing
      Φ Δᴸ Δᴿ ρ d d′ pC
      (endpoint-representatives-quotient D⊑E alignment)) →
  (up : OperationalUpCoercionNarrowing
    Φ Δᴸ Δᴿ ρ u u′
      (endpoint-representatives-quotient D⊑E alignment) pA) →
  (left-up-inert : Inert u) →
  (right-up-inert : Inert u′) →
  (value :
    FramedValueNarrowing
      {A = C} {A′ = C′} {p = pC} runtime V V′) →
  (left-down-frame :
    ClosedValueFrame θ V left-down-inert L) →
  (right-down-frame :
    ClosedValueFrame θ′ V′ right-down-inert L′) →
  (left-down-eq :
    ∀ n → coerceValue W θ d V (suc n)
      ≡ returned W L) →
  (right-down-eq :
    ∀ n → coerceValue W′ θ′ d′ V′ (suc n)
      ≡ returned W′ L′) →
  IndexedTerminalSimulation
    (FramedValueResult ρ θ θ′ pA) R
    (coerceValue W θ u L)
    (coerceValue W′ θ′ u′ L′)
    (suc left-index) (suc right-index)
indexed-quotient-up-inert
    runtime
    down@(paired-id-down-action source-down target-down)
    up@(paired-quotient-up-action widening)
    left-up-inert right-up-inert value
    left-down-frame right-down-frame
    left-down-eq right-down-eq
    with execute-inert-frame
      (left-runtime-context runtime)
      (proj₂ (quotient-up-left-typing up))
      left-up-inert
       | execute-inert-frame
      (right-runtime-context runtime)
      (proj₂ (quotient-up-right-typing up))
      right-up-inert
indexed-quotient-up-inert
    {left-index} {right-index}
    {D⊑E = D⊑E} {alignment = alignment} {pA = pA}
    runtime
    down@(paired-id-down-action source-down target-down)
    up@(paired-quotient-up-action widening)
    left-up-inert right-up-inert value
    left-down-frame right-down-frame
    left-down-eq right-down-eq
    | inert-frame-execution U left-up-frame left-up-eq
    | inert-frame-execution U′ right-up-frame right-up-eq =
  indexed-immediate-returns
    (left-up-eq left-index)
    (right-up-eq right-index)
    (left-up-eq zero)
    (right-up-eq zero)
    (framed-result runtime
      (framed-value output-typed output-operational
        (operational-quotient-originᶠ
          D⊑E alignment down up quotient-frame value)))
  where
  input = framed-value-typed value

  left-down-typed =
    returned-value-typing
      (coerceValue-preserves-semantic-typing
        (suc zero)
        (left-world-typed input)
        (left-runtime-context runtime)
        (proj₁ source-down)
        (left-value-typed input))
      (left-down-eq zero)

  right-down-typed =
    returned-value-typing
      (coerceValue-preserves-semantic-typing
        (suc zero)
        (right-world-typed input)
        (right-runtime-context runtime)
        (proj₁ target-down)
        (right-value-typed input))
      (right-down-eq zero)

  left-output-typed =
    returned-value-typing
      (coerceValue-preserves-semantic-typing
        (suc zero)
        (left-world-typed input)
        (left-runtime-context runtime)
        (proj₂ (quotient-up-left-typing up))
        left-down-typed)
      (left-up-eq zero)

  right-output-typed =
    returned-value-typing
      (coerceValue-preserves-semantic-typing
        (suc zero)
        (right-world-typed input)
        (right-runtime-context runtime)
        (proj₂ (quotient-up-right-typing up))
        right-down-typed)
      (right-up-eq zero)

  quotient-frame =
    quotient-value-frame
      source-down target-down D⊑E alignment widening pA
      (runtime-narrowing-frame runtime)
      left-down-frame right-down-frame
      left-up-frame right-up-frame

  output-typed =
    typed-value-narrowing
      (quotient-value-frame⊑ quotient-frame
        (semantic-value-scoped left-output-typed)
        (semantic-value-scoped right-output-typed)
        (values-narrow input))
      (left-world-typed input)
      (right-world-typed input)
      left-output-typed
      right-output-typed

  output-operational =
    operational-value output-typed
      (operational-quotient-origin
        runtime D⊑E alignment down up refl refl quotient-frame
        (framed-value-operational value))

indexed-quotient-up-inert
    runtime
    down@(paired-generalized-down-action source-down target-down)
    up@(paired-quotient-up-action widening)
    left-up-inert right-up-inert value
    left-down-frame right-down-frame
    left-down-eq right-down-eq
    with execute-inert-frame
      (left-runtime-context runtime)
      (proj₂ (quotient-up-left-typing up))
      left-up-inert
       | execute-inert-frame
      (right-runtime-context runtime)
      (proj₂ (quotient-up-right-typing up))
      right-up-inert
indexed-quotient-up-inert
    {left-index} {right-index}
    {D⊑E = D⊑E} {alignment = alignment} {pA = pA}
    runtime
    down@(paired-generalized-down-action source-down target-down)
    up@(paired-quotient-up-action widening)
    left-up-inert right-up-inert value
    left-down-frame right-down-frame
    left-down-eq right-down-eq
    | inert-frame-execution U left-up-frame left-up-eq
    | inert-frame-execution U′ right-up-frame right-up-eq =
  indexed-immediate-returns
    (left-up-eq left-index)
    (right-up-eq right-index)
    (left-up-eq zero)
    (right-up-eq zero)
    (framed-result runtime
      (framed-value output-typed output-operational
        (operational-quotient-originᶠ
          D⊑E alignment down up quotient-frame value)))
  where
  input = framed-value-typed value

  left-down-typed =
    returned-value-typing
      (coerceValue-preserves-semantic-typing
        (suc zero)
        (left-world-typed input)
        (left-runtime-context runtime)
        (proj₁ source-down)
        (left-value-typed input))
      (left-down-eq zero)

  right-down-typed =
    returned-value-typing
      (coerceValue-preserves-semantic-typing
        (suc zero)
        (right-world-typed input)
        (right-runtime-context runtime)
        (proj₁ target-down)
        (right-value-typed input))
      (right-down-eq zero)

  left-output-typed =
    returned-value-typing
      (coerceValue-preserves-semantic-typing
        (suc zero)
        (left-world-typed input)
        (left-runtime-context runtime)
        (proj₂ (quotient-up-left-typing up))
        left-down-typed)
      (left-up-eq zero)

  right-output-typed =
    returned-value-typing
      (coerceValue-preserves-semantic-typing
        (suc zero)
        (right-world-typed input)
        (right-runtime-context runtime)
        (proj₂ (quotient-up-right-typing up))
        right-down-typed)
      (right-up-eq zero)

  quotient-frame =
    quotient-value-frame
      source-down target-down D⊑E alignment widening pA
      (runtime-narrowing-frame runtime)
      left-down-frame right-down-frame
      left-up-frame right-up-frame

  output-typed =
    typed-value-narrowing
      (quotient-value-frame⊑ quotient-frame
        (semantic-value-scoped left-output-typed)
        (semantic-value-scoped right-output-typed)
        (values-narrow input))
      (left-world-typed input)
      (right-world-typed input)
      left-output-typed
      right-output-typed

  output-operational =
    operational-value output-typed
      (operational-quotient-origin
        runtime D⊑E alignment down up refl refl quotient-frame
        (framed-value-operational value))

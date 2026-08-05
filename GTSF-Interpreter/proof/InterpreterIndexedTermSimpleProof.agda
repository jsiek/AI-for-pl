module proof.InterpreterIndexedTermSimpleProof where

-- File Charter:
--   * Proves indexed variable, closure, and constant interpreter simulation.
--   * Upgrades the checked value-only cases with exact producer origins.
--   * Uses interpreter equations, typing, and world weakening only.

open import Data.List using (_∷_)
open import Data.Product using (_,_)

open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import Interpreter
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Runtime.InterpreterOperationalEnvironmentLookup
open import Narrowing.InterpreterOperationalValueNarrowing
open import Narrowing.InterpreterOperationalValueNarrowingProperties
import Runtime.InterpreterRuntimeFrame as Frame
open import Typing.InterpreterSemanticTypingCore
open import Simulation.Core.InterpreterSimulationContext
open import Simulation.Core.InterpreterSimulationContextProperties
open import Narrowing.InterpreterTermNarrowing
open import Narrowing.InterpreterTermNarrowingInversion
open import Simulation.Core.InterpreterTermSimulationSimple
open import Simulation.Core.InterpreterTermSimulationTyping
open import Narrowing.InterpreterTypedValueNarrowing
open import Runtime.InterpreterTypeEnvironmentRealization
import NuTermImprecision as NTI
import NuTerms as N
import Primitives
import TermTyping as TT
open import proof.InterpreterIndexedResultMap using
  (indexed-result-map)
open import proof.InterpreterIndexedSimulationTransport using
  (indexed-simulation-pointwise)
open import proof.InterpreterSimulationHelpers using
  (immediate-return-simulation)
import proof.InterpreterTermSimulationSimpleCases as Simple
open import proof.InterpreterRuntimeFramePrefix using
  (runtime-frame-prefix)
import proof.InterpreterSemanticTypingProperties as SemanticProof
open import Types

open Narrowing.InterpreterTermNarrowing.RelatedWorlds

closure-origin-aligned :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ γᵀ θ θ′ γ γ′
      N N′ A A′ B B′ pA pB}
    {R : WorldRelation W W′} →
  AlignedInterpreterTermNarrowing
    Φ Δᴸ Δᴿ ρ γᵀ
    (N.ƛ N) (N.ƛ N′)
    (A ⇒ B) (A′ ⇒ B′) (pA ImprecisionWf.↦ pB) →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  OperationalEnvironmentNarrowing θ θ′ R γᵀ γ γ′ →
  OperationalValueOrigin
    (⟦ A ⟧[ θ ] ⇒ᵛ ⟦ B ⟧[ θ ])
    (⟦ A′ ⟧[ θ′ ] ⇒ᵛ ⟦ B′ ⟧[ θ′ ])
    R (closure N γ θ) (closure N′ γ′ θ′)
closure-origin-aligned
    (closure-aligned hA hA′ body)
    runtime environment origins =
  closure-origin runtime environment origins
    (open-interpreter-narrowing body)
closure-origin-aligned
    (allocation-prefix-aligned prefix body source target)
    runtime environment origins =
  closure-origin-aligned body
    (runtime-narrowing-from-frame
      (left-world-typed runtime)
      (right-world-typed runtime)
      (assumption-membership-unique runtime)
      (runtime-frame-prefix prefix
        (runtime-narrowing-frame runtime)))
    (environment-realization
      (environments-narrow environment)
      (left-environment-typed environment)
      (right-environment-typed environment))
    origins

closure-open-body-aligned :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ γᵀ N N′ A A′ B B′ pA pB}
    {R : WorldRelation W W′} →
  AlignedInterpreterTermNarrowing
    Φ Δᴸ Δᴿ ρ γᵀ
    (N.ƛ N) (N.ƛ N′)
    (A ⇒ B) (A′ ⇒ B′) (pA ImprecisionWf.↦ pB) →
  OpenInterpreterTermNarrowing R Φ Δᴸ Δᴿ ρ
    (NTI.ctx-imp A A′ pA ∷ γᵀ) N N′ B B′ pB
closure-open-body-aligned
    (closure-aligned hA hA′ body) =
  open-interpreter-narrowing body
closure-open-body-aligned
    {R = R}
    (allocation-prefix-aligned prefix body
      (TT.⊢ƛ hA source-body) (TT.⊢ƛ hA′ target-body)) =
  open-interpreter-narrowing
    (allocation-prefix-aligned prefix
      (term-alignment
        (closure-open-body-aligned {R = R} body))
      source-body target-body)

indexed-variable-simulation :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ ρ γᵀ
      θ θ′ γ γ′ x A A′}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  OperationalEnvironmentNarrowing θ θ′ R γᵀ γ γ′ →
  γᵀ ∋ x ⦂ NTI.ctx-imp A A′ p →
  IndexedTerminalSimulation
    (OperationalValueResult ⟦ A ⟧[ θ ] ⟦ A′ ⟧[ θ′ ])
    R
    (interpret W γ θ (N.` x))
    (interpret W′ γ′ θ′ (N.` x))
    left-index right-index
indexed-variable-simulation environment origins x∈
    with operational-environment-lookup origins x∈
indexed-variable-simulation environment origins x∈
    | V , V′ , left-eq , right-eq , value =
  indexed-simulation-pointwise
    (Simple.variable-computation-eq left-eq)
    (Simple.variable-computation-eq right-eq)
    (terminal-simulation-index
      (immediate-return-simulation value))

indexed-closure-simulation :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ ρ γᵀ
      θ θ′ γ γ′ N N′ A A′ B B′ pA pB}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  OperationalEnvironmentNarrowing θ θ′ R γᵀ γ γ′ →
  (terms :
    OpenInterpreterTermNarrowing R Φ Δᴸ Δᴿ ρ γᵀ
      (N.ƛ N) (N.ƛ N′)
      (A ⇒ B) (A′ ⇒ B′) (pA ImprecisionWf.↦ pB)) →
  IndexedTerminalSimulation
    (OperationalValueResult
      (⟦ A ⟧[ θ ] ⇒ᵛ ⟦ B ⟧[ θ ])
      (⟦ A′ ⟧[ θ′ ] ⇒ᵛ ⟦ B′ ⟧[ θ′ ]))
    R
    (interpret W γ θ (N.ƛ N))
    (interpret W′ γ′ θ′ (N.ƛ N′))
    left-index right-index
indexed-closure-simulation
    {runtime = runtime} environment origins terms =
  indexed-simulation-pointwise
    Simple.closure-computation-eq
    Simple.closure-computation-eq
    (terminal-simulation-index
      (immediate-return-simulation
        (operational-value typed origin)))
  where
  body =
    closure-open-body-aligned (term-alignment terms)

  values =
    InterpreterValues.closure⊑
      (persistent-body-narrowing
        body
        (runtime-narrowing-frame runtime)
        (λ R≤S U⊢ →
          SemanticProof.environment-weaken
            (Frame.left-world-extension R≤S) U⊢
            (left-environment-typed environment))
        (λ R≤S U′⊢ →
          SemanticProof.environment-weaken
            (Frame.right-world-extension R≤S) U′⊢
            (right-environment-typed environment)))
      (environments-narrow environment)
      (TypeEnvironmentRealization.environments-narrow
        (type-environments-realized runtime))

  left-body-typing =
    open-interpreter-narrowing-source-typing body

  right-body-typing =
    open-interpreter-narrowing-target-typing body

  typed =
    typed-value-narrowing values
      (left-world-typed runtime)
      (right-world-typed runtime)
      (closure-typed
        (left-world-typed runtime)
        (left-runtime-context runtime)
        (left-environment-typed environment)
        (interpreter-narrowing-source-term (term-shape body))
        (TT.forget left-body-typing))
      (closure-typed
        (right-world-typed runtime)
        (right-runtime-context runtime)
        (right-environment-typed environment)
        (interpreter-narrowing-target-term (term-shape body))
        (TT.forget right-body-typing))

  origin =
    closure-origin-aligned
      (term-alignment terms) runtime environment origins

indexed-constant-simulation :
  ∀ {left-index right-index W W′ γ γ′ θ θ′ n}
    {R : WorldRelation W W′} →
  WorldTyping W →
  WorldTyping W′ →
  IndexedTerminalSimulation
    (OperationalValueResult
      (base-type `ℕ) (base-type `ℕ))
    R
    (interpret W γ θ (N.$ (Primitives.κℕ n)))
    (interpret W′ γ′ θ′ (N.$ (Primitives.κℕ n)))
    left-index right-index
indexed-constant-simulation {n = n} W⊢ W′⊢ =
  indexed-simulation-pointwise
    Simple.constant-computation-eq
    Simple.constant-computation-eq
    (terminal-simulation-index
      (immediate-return-simulation
        (operational-value
          (typed-value-narrowing
            (InterpreterValues.constant⊑ (Primitives.κℕ n))
            W⊢ W′⊢ constant-typed constant-typed)
          constant-origin)))

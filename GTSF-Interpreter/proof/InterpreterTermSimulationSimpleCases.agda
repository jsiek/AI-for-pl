module proof.InterpreterTermSimulationSimpleCases where

-- File Charter:
--   * Proves variable, closure, and constant interpreter simulation cases.
--   * Uses synchronized runtime environments and immediate-result algebra.
--   * Leaves applications, polymorphism, coercions, and allocation to their
--     focused case modules.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (_∷_)
open import Data.Maybe using (just)
import Data.Nat
open import Data.Product using (_,_)

open import Interpreter
open import Narrowing.InterpreterEnvironmentNarrowing
open import Typing.InterpreterSemanticTyping
import Runtime.InterpreterRuntimeFrame as Frame
open import Simulation.Core.InterpreterSimulationContext
open import Simulation.Core.InterpreterSimulationResult
open import Narrowing.InterpreterTermNarrowing
open import Runtime.InterpreterTypeEnvironmentRealization
import NuTermImprecision as NTI
import NuTerms as N
open import Primitives using (Const)
open import proof.InterpreterSimulationHelpers using
  (immediate-return-simulation)
open import proof.InterpreterSimulationTransport using
  (simulation-pointwise)
import proof.InterpreterSemanticTypingProperties as SemanticProof
open import Types

open InterpreterValues
open Narrowing.InterpreterTermNarrowing.RelatedWorlds

module Environments =
  Narrowing.InterpreterEnvironmentNarrowing.EnvironmentNarrowing
    interpreterNarrowingLeaves

variable-computation-eq :
  ∀ {W γ θ x V} →
  lookup γ x Agda.Builtin.Equality.≡ just V →
  ∀ n →
  interpret W γ θ (N.` x) n
    Agda.Builtin.Equality.≡ immediateReturn W V n
variable-computation-eq lookup-eq Data.Nat.zero =
  Agda.Builtin.Equality.refl
variable-computation-eq lookup-eq (Data.Nat.suc n)
    rewrite lookup-eq =
  Agda.Builtin.Equality.refl

closure-computation-eq :
  ∀ {W γ θ N} n →
  interpret W γ θ (N.ƛ N) n ≡
  immediateReturn W (closure N γ θ) n
closure-computation-eq Data.Nat.zero =
  refl
closure-computation-eq (Data.Nat.suc n) =
  refl

constant-computation-eq :
  ∀ {W γ θ κ} n →
  interpret W γ θ (N.$ κ) n ≡
  immediateReturn W (constant κ) n
constant-computation-eq Data.Nat.zero =
  refl
constant-computation-eq (Data.Nat.suc n) =
  refl

variable-simulation :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ γᵀ θ θ′ γ γ′ x A B p}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  γᵀ ∋ x ⦂ NTI.ctx-imp A B p →
  TerminalSimulation ValueNarrowing R
    (interpret W γ θ (N.` x))
    (interpret W′ γ′ θ′ (N.` x))
variable-simulation environment x∈
    with term-environment-lookup
      (left-environment-typed environment)
      (NTI.leftCtxⁱ-∋ x∈)
variable-simulation environment x∈
    | V , left-eq , V⊢
    with Environments.environment-lookup-narrowing
      (EnvironmentRealization.environments-narrow environment)
      left-eq
variable-simulation environment x∈
    | V , left-eq , V⊢
    | V′ , right-eq , V~V′
    =
  simulation-pointwise
    (variable-computation-eq left-eq)
    (variable-computation-eq right-eq)
    (immediate-return-simulation V~V′)

closure-simulation :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ γᵀ θ θ′ γ γ′ N N′}
    {A A′ B B′ pA pB}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  EnvironmentRealization runtime γᵀ γ γ′ →
  OpenInterpreterTermNarrowing
    R Φ Δᴸ Δᴿ ρ (NTI.ctx-imp A A′ pA ∷ γᵀ)
    N N′ B B′ pB →
  TerminalSimulation ValueNarrowing R
    (interpret W γ θ (N.ƛ N))
    (interpret W′ γ′ θ′ (N.ƛ N′))
closure-simulation {runtime = runtime} environment body =
  simulation-pointwise
    closure-computation-eq
    closure-computation-eq
    (immediate-return-simulation
      (closure⊑
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
        (EnvironmentRealization.environments-narrow environment)
        (TypeEnvironmentRealization.environments-narrow
          (type-environments-realized runtime))))

constant-simulation :
  ∀ {W W′ γ γ′ θ θ′}
    {R : WorldRelation W W′} →
  (κ : Const) →
  TerminalSimulation ValueNarrowing R
    (interpret W γ θ (N.$ κ))
    (interpret W′ γ′ θ′ (N.$ κ))
constant-simulation κ =
  simulation-pointwise
    constant-computation-eq
    constant-computation-eq
    (immediate-return-simulation (constant⊑ κ))

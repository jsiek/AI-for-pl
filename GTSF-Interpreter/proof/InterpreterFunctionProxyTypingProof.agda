module proof.InterpreterFunctionProxyTypingProof where

-- File Charter:
--   * Proves unary error freedom for proxy tails and whole proxy application.
--   * Threads semantic typing through application and the codomain coercion.
--   * Uses no narrowing, small-step semantics, or reduction-derived theorem.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (subst)

open import Coercions
open import Interpreter
open import Typing.InterpreterErrorFreedom using
  (outcome-typing-excludes-error)
open import Typing.InterpreterSemanticTypingCore
open import proof.InterpreterFunctionProxyTail
import proof.InterpreterSemanticTypingProperties as Properties
import proof.InterpreterTypingCore as Typing

function-proxy-tail-typing :
  ∀ {W Δ Σ θ q V U A B C μ} →
  WorldTyping W →
  RuntimeContext W Δ Σ θ →
  μ ∣ Δ ∣ Σ ⊢ q ∶ B =⇒ C →
  ValueTyping W V (⟦ A ⟧[ θ ] ⇒ᵛ ⟦ B ⟧[ θ ]) →
  ValueTyping W U ⟦ A ⟧[ θ ] →
  ∀ n →
  OutcomeTyping W ⟦ C ⟧[ θ ]
    (function-proxy-tail θ q V W U n)
function-proxy-tail-typing
    {W} {Δ} {Σ} {θ} {q} {V} {U} {A} {B} {C} {μ}
    W⊢ runtime q⊢ V⊢ U⊢ n
    with applyValue W V U n in apply-eq
function-proxy-tail-typing
    {W} {Δ} {Σ} {θ} {q} {V} {U} {A} {B} {C} {μ}
    W⊢ runtime q⊢ V⊢ U⊢ n
    | result
    with subst (OutcomeTyping W ⟦ B ⟧[ θ ]) apply-eq
      (Typing.applyValue-typing n W⊢ V⊢ U⊢)
function-proxy-tail-typing
    W⊢ runtime q⊢ V⊢ U⊢ n
    | timed Z | timeout-typed W≤Z =
  timeout-typed W≤Z
function-proxy-tail-typing
    W⊢ runtime q⊢ V⊢ U⊢ n
    | blamed Z | blame-typed W≤Z =
  blame-typed W≤Z
function-proxy-tail-typing
    W⊢ runtime q⊢ V⊢ U⊢ n
    | failed Z e | ()
function-proxy-tail-typing
    {W} {Δ} {Σ} {θ} {q} {V} {U} {A} {B} {C} {μ}
    W⊢ runtime q⊢ V⊢ U⊢ n
    | returned Z Q | return-typed W≤Z Z⊢ Q⊢ =
  Properties.outcome-rebase W≤Z
    (Typing.coerceValue-typing n Z⊢
      (Properties.runtime-context-weaken W≤Z runtime)
      q⊢ Q⊢)

function-proxy-tail-error-impossible :
  ∀ {W Δ Σ θ q V U A B C μ n Z e} →
  WorldTyping W →
  RuntimeContext W Δ Σ θ →
  μ ∣ Δ ∣ Σ ⊢ q ∶ B =⇒ C →
  ValueTyping W V (⟦ A ⟧[ θ ] ⇒ᵛ ⟦ B ⟧[ θ ]) →
  ValueTyping W U ⟦ A ⟧[ θ ] →
  function-proxy-tail θ q V W U n ≡ failed Z e →
  ⊥
function-proxy-tail-error-impossible
    {W} {Δ} {Σ} {θ} {q} {V} {U}
    {A} {B} {C} {μ} {n}
    W⊢ runtime q⊢ V⊢ U⊢ result-eq =
  outcome-typing-excludes-error
    (function-proxy-tail-typing
      {W = W} {Δ = Δ} {Σ = Σ} {θ = θ}
      {q = q} {V = V} {U = U}
      {A = A} {B = B} {C = C} {μ = μ}
      W⊢ runtime q⊢ V⊢ U⊢ n)
    result-eq

function-proxy-application-error-impossible :
  ∀ {W θ p q V U A B n Z e} →
  WorldTyping W →
  ValueTyping W (function-proxy p q θ V) (A ⇒ᵛ B) →
  ValueTyping W U A →
  applyValue W (function-proxy p q θ V) U n ≡
    failed Z e →
  ⊥
function-proxy-application-error-impossible
    {W} {θ} {p} {q} {V} {U} {A} {B} {n}
    W⊢ proxy⊢ U⊢ result-eq =
  outcome-typing-excludes-error
    (Typing.applyValue-typing
      n {W = W} {A = A} {B = B}
      {V = function-proxy p q θ V} {U = U}
      W⊢ proxy⊢ U⊢)
    result-eq

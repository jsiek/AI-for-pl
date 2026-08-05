module proof.InterpreterForallProxyTypingProof where

-- File Charter:
--   * Proves unary error freedom for whole forall-proxy instantiation.
--   * Reuses direct interpreter semantic typing and allocation evidence.
--   * Uses no narrowing, small-step semantics, or reduction-derived theorem.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

open import Interpreter
open import Typing.InterpreterErrorFreedom using
  (outcome-typing-excludes-error)
open import Typing.InterpreterSemanticTypingCore
open import Narrowing.InterpreterWorldNarrowing using (Allocated)
import proof.InterpreterTypingCore as Typing

forall-proxy-instantiation-error-impossible :
  ∀ {W α c θ V body n Z e} →
  WorldTyping W →
  Allocated W α →
  ValueTyping W (forall-proxy c θ V)
    (polymorphic-type body) →
  instantiateValue W α (forall-proxy c θ V) n ≡
    failed Z e →
  ⊥
forall-proxy-instantiation-error-impossible
    {W} {α} {c} {θ} {V} {body} {n}
    W⊢ α-ok proxy⊢ result-eq =
  outcome-typing-excludes-error
    (Typing.instantiateValue-typing
      n {W = W} {V = forall-proxy c θ V}
      {body = body} {α = α}
      W⊢ α-ok proxy⊢)
    result-eq

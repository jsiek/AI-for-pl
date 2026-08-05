module Typing.InterpreterForallProxyTyping where

-- File Charter:
--   * Exposes unary error freedom for whole forall-proxy instantiation.
--   * Makes world allocation and semantic proxy typing inputs explicit.
--   * Delegates the semantic-typing argument to its private proof module.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

open import Interpreter
open import Typing.InterpreterSemanticTypingCore
open import Narrowing.InterpreterWorldNarrowing using (Allocated)
import proof.InterpreterForallProxyTypingProof as Proof

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
    {W} {α} {c} {θ} {V} {body} {n} {Z} {e}
    W⊢ α-ok proxy⊢ result-eq =
  Proof.forall-proxy-instantiation-error-impossible
    {W = W} {α = α} {c = c} {θ = θ} {V = V}
    {body = body} {n = n} {Z = Z} {e = e}
    W⊢ α-ok proxy⊢ result-eq

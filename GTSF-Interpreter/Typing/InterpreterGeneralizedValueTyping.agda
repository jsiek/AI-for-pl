module Typing.InterpreterGeneralizedValueTyping where

-- File Charter:
--   * Exposes unary error freedom for generalized-value instantiation.
--   * Makes world allocation and semantic value typing inputs explicit.
--   * Delegates the semantic-typing argument to its private proof module.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

open import Interpreter
open import Typing.InterpreterSemanticTypingCore
open import Narrowing.InterpreterWorldNarrowing using (Allocated)
import proof.InterpreterGeneralizedValueTypingProof as Proof

generalized-value-instantiation-error-impossible :
  ∀ {W α A c θ V body n Z e} →
  WorldTyping W →
  Allocated W α →
  ValueTyping W (generalized A c θ V)
    (polymorphic-type body) →
  instantiateValue W α (generalized A c θ V) n ≡
    failed Z e →
  ⊥
generalized-value-instantiation-error-impossible
    {W} {α} {A} {c} {θ} {V} {body} {n} {Z} {e}
    W⊢ α-ok generalized⊢ result-eq =
  Proof.generalized-value-instantiation-error-impossible
    {W = W} {α = α} {A = A} {c = c}
    {θ = θ} {V = V} {body = body}
    {n = n} {Z = Z} {e = e}
    W⊢ α-ok generalized⊢ result-eq

module Typing.InterpreterFunctionProxyTyping where

-- File Charter:
--   * Exposes unary error freedom for the two proxy-application computations.
--   * Makes all semantic typing and coercion typing inputs explicit.
--   * Delegates proof recursion to its private proof module.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

open import Coercions
open import Interpreter
open import Typing.InterpreterSemanticTypingCore
open import proof.InterpreterFunctionProxyTail using
  (function-proxy-tail)
import proof.InterpreterFunctionProxyTypingProof as Proof

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
    {A} {B} {C} {μ} {n} {Z} {e}
    W⊢ runtime q⊢ V⊢ U⊢ result-eq =
  Proof.function-proxy-tail-error-impossible
    {W = W} {Δ = Δ} {Σ = Σ} {θ = θ}
    {q = q} {V = V} {U = U}
    {A = A} {B = B} {C = C} {μ = μ}
    {n = n} {Z = Z} {e = e}
    W⊢ runtime q⊢ V⊢ U⊢ result-eq

function-proxy-application-error-impossible :
  ∀ {W θ p q V U A B n Z e} →
  WorldTyping W →
  ValueTyping W (function-proxy p q θ V) (A ⇒ᵛ B) →
  ValueTyping W U A →
  applyValue W (function-proxy p q θ V) U n ≡
    failed Z e →
  ⊥
function-proxy-application-error-impossible
    {W} {θ} {p} {q} {V} {U} {A} {B} {n} {Z} {e}
    W⊢ proxy⊢ U⊢ result-eq =
  Proof.function-proxy-application-error-impossible
    {W = W} {θ = θ} {p = p} {q = q}
    {V = V} {U = U} {A = A} {B = B}
    {n = n} {Z = Z} {e = e}
    W⊢ proxy⊢ U⊢ result-eq

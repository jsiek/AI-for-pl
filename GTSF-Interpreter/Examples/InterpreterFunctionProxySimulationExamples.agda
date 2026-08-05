module Examples.InterpreterFunctionProxySimulationExamples where

-- File Charter:
--   * Checks the direct function-proxy computation equation by normalization.
--   * Exercises domain coercion, closure application, and codomain coercion.
--   * Uses a first-order result so the complete proxy path is observable.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([])
open import Data.Nat using (zero; suc)

import Coercions
open import Interpreter
import NuTerms as N
open import Primitives using (κℕ)
open import Types

Nat : Ty
Nat =
  ‵ `ℕ

identity-proxy : Value
identity-proxy =
  function-proxy
    (Coercions.id Nat)
    (Coercions.id Nat)
    []
    (closure (N.` zero) [] [])

identity-proxy-result :
  applyValue emptyWorld identity-proxy
    (constant (κℕ 7))
    (suc (suc (suc zero))) ≡
  returned emptyWorld (constant (κℕ 7))
identity-proxy-result =
  refl

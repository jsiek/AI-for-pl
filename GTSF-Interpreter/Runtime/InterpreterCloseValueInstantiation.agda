module Runtime.InterpreterCloseValueInstantiation where

-- File Charter:
--   * States exact closing under an abstract name followed by instantiation.
--   * Uses the deterministic abstract-name supply of `closeValue`.
--   * Contains no interpreter recursion, reduction, or catch-up theorem.
--   * Delegates the structural proof to a private proof module.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using (_∷_)
open import Data.Maybe using (just)

open import Interpreter
import NuTerms as N
import proof.InterpreterCloseValueInstantiationProof as Proof


closeValue-instantiate-generated :
  ∀ {M γ θ U α}
    (vM : N.Value M) →
  closeValue vM γ
    (abstract-name (nextAbstractName θ) ∷ θ) ≡ just U →
  closeValue vM γ (seal-name α ∷ θ) ≡
    just (substituteName (nextAbstractName θ) α U)
closeValue-instantiate-generated =
  Proof.closeValue-instantiate-generated

module Typing.InterpreterCoercionSemanticTyping where

-- File Charter:
--   * Public unary semantic typing and error freedom for `coerceValue`.
--   * Keeps semantic blame while excluding interpreter implementation errors.
--   * Delegates the mutual fuel induction to existing private typing proofs.

open import Coercions using
  (ModeEnv; Coercion; _∣_∣_⊢_∶_=⇒_)
open import Relation.Binary.PropositionalEquality using (_≢_)

open import Interpreter
open import Typing.InterpreterSemanticTypingCore
open import Types
import proof.InterpreterErrorFreedomCore as ErrorProof
import proof.InterpreterTypingCore as Proof

coerceValue-preserves-semantic-typing :
  ∀ n {W Δ Σ θ c V A B μ} →
  WorldTyping W →
  RuntimeContext W Δ Σ θ →
  RuntimeTypeEnvironment θ →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B →
  ValueTyping W V ⟦ A ⟧[ θ ] →
  OutcomeTyping W ⟦ B ⟧[ θ ]
    (coerceValue W θ c V n)
coerceValue-preserves-semantic-typing =
  Proof.coerceValue-typing

coerceValue-never-fails :
  ∀ n {W Δ Σ θ c V A B μ U e} →
  WorldTyping W →
  RuntimeContext W Δ Σ θ →
  RuntimeTypeEnvironment θ →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B →
  ValueTyping W V ⟦ A ⟧[ θ ] →
  coerceValue W θ c V n ≢ failed U e
coerceValue-never-fails n W⊢ runtime runtime-env c⊢ V⊢ =
  ErrorProof.outcome-typing-excludes-error
    (coerceValue-preserves-semantic-typing
      n W⊢ runtime runtime-env c⊢ V⊢)

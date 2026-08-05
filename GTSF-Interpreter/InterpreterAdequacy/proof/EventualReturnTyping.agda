module InterpreterAdequacy.proof.EventualReturnTyping where

-- File Charter:
--   * Extracts world and value typing from successful generalized interpreter
--     calls used by the completeness driver.
--   * Keeps all four extraction lemmas independent of small-step reduction.
--   * Delegates error freedom to the established unary typing induction.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (subst)

import Coercions as C
open import Interpreter
open import Typing.InterpreterSemanticTypingCore
open import SmallStepInterface.InterpreterTermShape using (InterpreterTerm)
open import Narrowing.InterpreterWorldNarrowing using (Allocated)
import NuTerms as N
open import proof.InterpreterTypingCore using
  ( applyValue-typing
  ; coerceValue-typing
  ; instantiateValue-typing
  ; interpret-typing
  )

returned-outcome-typing :
  ∀ {W U V A} →
  OutcomeTyping W A (returned U V) →
  WorldExtension W U × (WorldTyping U × ValueTyping U V A)
returned-outcome-typing (return-typed W≤U U⊢ V⊢) = W≤U , U⊢ , V⊢

interpret-returned-typing :
  ∀ n {W Δ Σ Γ θ γ M A U V} →
  (W⊢ : WorldTyping W) →
  (runtime : RuntimeContext W Δ Σ θ) →
  (runtime-env : RuntimeTypeEnvironment θ) →
  (environment : EnvironmentTyping W θ γ Γ) →
  (image : InterpreterTerm M) →
  (typing : N._∣_∣_⊢_⦂_ Δ Σ Γ M A) →
  interpret W γ θ M n ≡ returned U V →
  WorldExtension W U ×
    (WorldTyping U × ValueTyping U V ⟦ A ⟧[ θ ])
interpret-returned-typing n W⊢ runtime runtime-env environment image
    typing result-eq =
  returned-outcome-typing
    (subst (OutcomeTyping _ _) result-eq
      (interpret-typing n W⊢ runtime runtime-env environment image typing))

apply-returned-typing :
  ∀ n {W A B F U Z V} →
  (W⊢ : WorldTyping W) →
  ValueTyping W F (A ⇒ᵛ B) →
  ValueTyping W U A →
  applyValue W F U n ≡ returned Z V →
  WorldExtension W Z × (WorldTyping Z × ValueTyping Z V B)
apply-returned-typing n W⊢ F⊢ U⊢ result-eq =
  returned-outcome-typing
    (subst (OutcomeTyping _ _) result-eq
      (applyValue-typing n W⊢ F⊢ U⊢))

instantiate-returned-typing :
  ∀ n {W A α F Z V} →
  (W⊢ : WorldTyping W) →
  (allocated : Allocated W α) →
  ValueTyping W F (polymorphic-type A) →
  instantiateValue W α F n ≡ returned Z V →
  WorldExtension W Z ×
    (WorldTyping Z ×
      ValueTyping Z V
        (instantiateSemantic (nominal-type (seal-name α)) A))
instantiate-returned-typing n W⊢ allocation-ok F⊢ result-eq =
  returned-outcome-typing
    (subst (OutcomeTyping _ _) result-eq
      (instantiateValue-typing n W⊢ allocation-ok F⊢))

coerce-returned-typing :
  ∀ n {W Δ Σ θ c V A B μ Z U} →
  (W⊢ : WorldTyping W) →
  (runtime : RuntimeContext W Δ Σ θ) →
  (runtime-env : RuntimeTypeEnvironment θ) →
  (typing : C._∣_∣_⊢_∶_=⇒_ μ Δ Σ c A B) →
  ValueTyping W V ⟦ A ⟧[ θ ] →
  coerceValue W θ c V n ≡ returned Z U →
  WorldExtension W Z ×
    (WorldTyping Z × ValueTyping Z U ⟦ B ⟧[ θ ])
coerce-returned-typing n W⊢ runtime runtime-env typing V⊢ result-eq =
  returned-outcome-typing
    (subst (OutcomeTyping _ _) result-eq
      (coerceValue-typing n W⊢ runtime runtime-env typing V⊢))

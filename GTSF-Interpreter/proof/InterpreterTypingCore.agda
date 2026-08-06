module proof.InterpreterTypingCore where

-- File Charter:
--   * Proves the mutual semantic-typing theorem for `interpret`,
--     `applyValue`, `instantiateValue`, and `coerceValue`.
--   * Uses fuel as the sole recursion measure and eliminates every raw
--     interpreter-error branch.
--   * Contains no small-step relation, evaluation context, or reduction
--     theorem.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (just)
open import Data.Nat using (zero; suc)
open import Data.Product using (_,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import Coercions
open import Interpreter
open import Runtime.InterpreterClosedValue
open import Typing.InterpreterSemanticTypingCore
open import SmallStepInterface.InterpreterTermShape
import NuTerms as N
open import Primitives using (addℕ; κℕ)
open import proof.InterpreterClosedValueProof using
  (closeValue-closed; replaceName-head)
open import proof.InterpreterCloseValueTyping using
  (closeValue-defined; closedValue-typing;
   substituteName-closedValue-typing; syntacticValue-complete)
open import proof.InterpreterCoercionTyping using
  (ground?-complete; matching-tags-type-eq;
   runtime-ground-from-typing; tagOf-complete)
open import proof.InterpreterSemanticTypingProperties using
  (allocated-here; allocated-weaken; environment-lookup-sound;
   environment-type-weaken;
   environment-weaken; instantiate-interpret; interpret-weaken;
   outcome-rebase; outcome-type-transport; representation-functional;
   runtime-context-name; runtime-context-seal; runtime-context-weaken;
   semantic-name-lookup; store-lookup-sound; store-representation;
   value-weaken; world-extension-trans)
open import Narrowing.InterpreterWorldNarrowing using
  (Allocated; allocated; seal-scoped)
open import Types

------------------------------------------------------------------------
-- Mutual interpreter typing
------------------------------------------------------------------------

mutual

  interpret-typing :
    ∀ n {W Δ Σ Γ θ γ M A} →
    WorldTyping W →
    RuntimeContext W Δ Σ θ →
    RuntimeTypeEnvironment θ →
    EnvironmentTyping W θ γ Γ →
    InterpreterTerm M →
    N._∣_∣_⊢_⦂_ Δ Σ Γ M A →
    OutcomeTyping W ⟦ A ⟧[ θ ]
      (interpret W γ θ M n)

  applyValue-typing :
    ∀ n {W A B V U} →
    WorldTyping W →
    ValueTyping W V (A ⇒ᵛ B) →
    ValueTyping W U A →
    OutcomeTyping W B (applyValue W V U n)

  instantiateValue-typing :
    ∀ n {W V body α} →
    WorldTyping W →
    Allocated W α →
    ValueTyping W V (polymorphic-type body) →
    OutcomeTyping W
      (instantiateSemantic (nominal-type (seal-name α)) body)
      (instantiateValue W α V n)

  coerceValue-typing :
    ∀ n {W Δ Σ θ c V A B μ} →
    WorldTyping W →
    RuntimeContext W Δ Σ θ →
    RuntimeTypeEnvironment θ →
    μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B →
    ValueTyping W V ⟦ A ⟧[ θ ] →
    OutcomeTyping W ⟦ B ⟧[ θ ]
      (coerceValue W θ c V n)

  ----------------------------------------------------------------------
  -- Direct term interpretation
  ----------------------------------------------------------------------

  interpret-typing zero W⊢ runtime runtime-env γ⊢ image M⊢ =
    timeout-typed world-extension-refl

  interpret-typing (suc n) W⊢ runtime runtime-env γ⊢
      (variable-term x) (N.⊢` x∈)
      with environment-lookup-sound γ⊢ x∈
  interpret-typing (suc n) W⊢ runtime runtime-env γ⊢
      (variable-term x) (N.⊢` x∈)
      | V , lookup-eq , V⊢
      rewrite lookup-eq =
    return-typed world-extension-refl W⊢ V⊢

  interpret-typing (suc n) W⊢ runtime runtime-env γ⊢
      (closure-term body-image) (N.⊢ƛ hA body⊢) =
    return-typed world-extension-refl W⊢
      (closure-typed W⊢ runtime runtime-env γ⊢ body-image body⊢)

  interpret-typing (suc n) W⊢ runtime runtime-env γ⊢
      (application-term L-image M-image)
      (N.⊢· L⊢ M⊢)
      with interpret _ _ _ _ n in L-eq
  interpret-typing (suc n) W⊢ runtime runtime-env γ⊢
      (application-term L-image M-image)
      (N.⊢· L⊢ M⊢)
      | L-result
      with subst (OutcomeTyping _ _) L-eq
        (interpret-typing n W⊢ runtime runtime-env γ⊢ L-image L⊢)
  interpret-typing (suc n) W⊢ runtime runtime-env γ⊢
      (application-term L-image M-image)
      (N.⊢· L⊢ M⊢)
      | timed W₁ | timeout-typed W≤W₁
      rewrite L-eq =
    timeout-typed W≤W₁
  interpret-typing (suc n) W⊢ runtime runtime-env γ⊢
      (application-term L-image M-image)
      (N.⊢· L⊢ M⊢)
      | blamed W₁ | blame-typed W≤W₁
      rewrite L-eq =
    blame-typed W≤W₁
  interpret-typing (suc n) W⊢ runtime runtime-env γ⊢
      (application-term L-image M-image)
      (N.⊢· L⊢ M⊢)
      | failed W₁ e | ()
  interpret-typing (suc n) W⊢ runtime runtime-env γ⊢
      (application-term L-image M-image)
      (N.⊢· L⊢ M⊢)
      | returned W₁ V | return-typed W≤W₁ W₁⊢ V⊢
      rewrite L-eq
      with interpret W₁ _ _ _ n in M-eq
  interpret-typing (suc n) W⊢ runtime runtime-env γ⊢
      (application-term L-image M-image)
      (N.⊢· L⊢ M⊢)
      | returned W₁ V | return-typed W≤W₁ W₁⊢ V⊢
      | M-result
      with subst (OutcomeTyping _ _) M-eq
        (interpret-typing n W₁⊢
          (runtime-context-weaken W≤W₁ runtime)
          runtime-env
          (environment-weaken W≤W₁ W₁⊢ γ⊢)
          M-image M⊢)
  interpret-typing (suc n) W⊢ runtime runtime-env γ⊢
      (application-term L-image M-image)
      (N.⊢· L⊢ M⊢)
      | returned W₁ V | return-typed W≤W₁ W₁⊢ V⊢
      | timed W₂ | timeout-typed W₁≤W₂
      rewrite M-eq =
    timeout-typed (world-extension-trans W≤W₁ W₁≤W₂)
  interpret-typing (suc n) W⊢ runtime runtime-env γ⊢
      (application-term L-image M-image)
      (N.⊢· L⊢ M⊢)
      | returned W₁ V | return-typed W≤W₁ W₁⊢ V⊢
      | blamed W₂ | blame-typed W₁≤W₂
      rewrite M-eq =
    blame-typed (world-extension-trans W≤W₁ W₁≤W₂)
  interpret-typing (suc n) W⊢ runtime runtime-env γ⊢
      (application-term L-image M-image)
      (N.⊢· L⊢ M⊢)
      | returned W₁ V | return-typed W≤W₁ W₁⊢ V⊢
      | failed W₂ e | ()
  interpret-typing (suc n) W⊢ runtime runtime-env γ⊢
      (application-term L-image M-image)
      (N.⊢· L⊢ M⊢)
      | returned W₁ V | return-typed W≤W₁ W₁⊢ V⊢
      | returned W₂ U | return-typed W₁≤W₂ W₂⊢ U⊢
      rewrite M-eq =
    outcome-rebase
      (world-extension-trans W≤W₁ W₁≤W₂)
      (applyValue-typing n W₂⊢
        (value-weaken W₁≤W₂ W₂⊢ V⊢) U⊢)

  interpret-typing (suc n) W⊢ runtime runtime-env γ⊢
      (type-abstraction-term vImage body-image)
      (N.⊢Λ vTyping body⊢)
      with syntacticValue-complete vTyping
  interpret-typing (suc n) W⊢ runtime runtime-env γ⊢
      (type-abstraction-term vImage body-image)
      (N.⊢Λ vTyping body⊢)
      | vP , decision-eq
      rewrite decision-eq
      with closeValue-defined runtime γ⊢
        (type-abstraction-term vImage body-image)
        (N.Λ vP) (N.⊢Λ vTyping body⊢)
  interpret-typing (suc n) W⊢ runtime runtime-env γ⊢
      (type-abstraction-term vImage body-image)
      (N.⊢Λ vTyping body⊢)
      | vP , decision-eq
      | U , close-eq
      rewrite close-eq =
    return-typed world-extension-refl W⊢
      (closedValue-typing W⊢ runtime runtime-env γ⊢
        (type-abstraction-term vImage body-image)
        (N.⊢Λ vTyping body⊢)
        (closeValue-closed (N.Λ vP) close-eq))

  interpret-typing (suc n) {θ = θ} W⊢ runtime runtime-env γ⊢
      (instantiation-term L-image)
      (N.⊢ν hA L⊢ c⊢)
      with interpret _ _ _ _ n in L-eq
  interpret-typing (suc n) W⊢ runtime runtime-env γ⊢
      (instantiation-term L-image)
      (N.⊢ν hA L⊢ c⊢)
      | L-result
      with subst (OutcomeTyping _ _) L-eq
        (interpret-typing n W⊢ runtime runtime-env γ⊢ L-image L⊢)
  interpret-typing (suc n) W⊢ runtime runtime-env γ⊢
      (instantiation-term L-image)
      (N.⊢ν hA L⊢ c⊢)
      | timed W₁ | timeout-typed W≤W₁
      rewrite L-eq =
    timeout-typed W≤W₁
  interpret-typing (suc n) W⊢ runtime runtime-env γ⊢
      (instantiation-term L-image)
      (N.⊢ν hA L⊢ c⊢)
      | blamed W₁ | blame-typed W≤W₁
      rewrite L-eq =
    blame-typed W≤W₁
  interpret-typing (suc n) W⊢ runtime runtime-env γ⊢
      (instantiation-term L-image)
      (N.⊢ν hA L⊢ c⊢)
      | failed W₁ e | ()
  interpret-typing (suc n) W⊢ runtime runtime-env γ⊢
      (instantiation-term L-image)
      (N.⊢ν hA L⊢ c⊢)
      | returned W₁ V | return-typed W≤W₁ W₁⊢ V⊢
      rewrite L-eq
      with instantiateValue
        (allocate W₁ _ _) (freshSealName W₁) V n in inst-eq
  interpret-typing (suc n) W⊢ runtime runtime-env γ⊢
      (instantiation-term L-image)
      (N.⊢ν hA L⊢ c⊢)
      | returned W₁ V | return-typed W≤W₁ W₁⊢ V⊢
      | inst-result
      with subst (OutcomeTyping _ _) inst-eq
        (instantiateValue-typing n
          (allocate-world-typed W₁⊢
            (runtime-context-weaken W≤W₁ runtime) hA)
          allocated-here
          (value-weaken
            (world-extension-allocate world-extension-refl)
            (allocate-world-typed W₁⊢
              (runtime-context-weaken W≤W₁ runtime) hA)
            V⊢))
  interpret-typing (suc n) W⊢ runtime runtime-env γ⊢
      (instantiation-term L-image)
      (N.⊢ν hA L⊢ c⊢)
      | returned W₁ V | return-typed W≤W₁ W₁⊢ V⊢
      | timed W₂ | timeout-typed W₁⁺≤W₂
      rewrite inst-eq =
    timeout-typed
      (world-extension-trans W≤W₁
        (world-extension-trans
          (world-extension-allocate world-extension-refl)
          W₁⁺≤W₂))
  interpret-typing (suc n) W⊢ runtime runtime-env γ⊢
      (instantiation-term L-image)
      (N.⊢ν hA L⊢ c⊢)
      | returned W₁ V | return-typed W≤W₁ W₁⊢ V⊢
      | blamed W₂ | blame-typed W₁⁺≤W₂
      rewrite inst-eq =
    blame-typed
      (world-extension-trans W≤W₁
        (world-extension-trans
          (world-extension-allocate world-extension-refl)
          W₁⁺≤W₂))
  interpret-typing (suc n) W⊢ runtime runtime-env γ⊢
      (instantiation-term L-image)
      (N.⊢ν hA L⊢ c⊢)
      | returned W₁ V | return-typed W≤W₁ W₁⊢ V⊢
      | failed W₂ e | ()
  interpret-typing (suc n) {θ = θ} W⊢ runtime runtime-env γ⊢
      (instantiation-term L-image)
      (N.⊢ν {A = A} {B = B} {C = C}
        hA L⊢ c⊢)
      | returned W₁ V | return-typed W≤W₁ W₁⊢ V⊢
      | returned W₂ U | return-typed W₁⁺≤W₂ W₂⊢ U⊢
      rewrite inst-eq =
    outcome-type-transport
      (interpret-weaken
        (nominal-type (seal-name (freshSealName W₁)))
        (semanticEnvironment θ) B)
      (outcome-rebase
        (world-extension-trans W≤W₁
          (world-extension-trans
            (world-extension-allocate world-extension-refl)
            W₁⁺≤W₂))
        (coerceValue-typing n W₂⊢
          (runtime-context-weaken W₁⁺≤W₂
            (runtime-context-seal
              (runtime-context-weaken W≤W₁ runtime)))
          (runtime-type-seal runtime-env)
          c⊢
          (subst (ValueTyping W₂ U)
            (instantiate-interpret
              (nominal-type
                (seal-name (freshSealName W₁)))
              θ C)
            U⊢)))

  interpret-typing (suc n) W⊢ runtime runtime-env γ⊢
      (constant-term (κℕ k)) (N.⊢$ .(κℕ k)) =
    return-typed world-extension-refl W⊢ constant-typed

  interpret-typing (suc n) W⊢ runtime runtime-env γ⊢
      (primitive-term addℕ L-image M-image)
      (N.⊢⊕ L⊢ addℕ M⊢)
      with interpret _ _ _ _ n in L-eq
  interpret-typing (suc n) W⊢ runtime runtime-env γ⊢
      (primitive-term addℕ L-image M-image)
      (N.⊢⊕ L⊢ addℕ M⊢)
      | L-result
      with subst (OutcomeTyping _ _) L-eq
        (interpret-typing n W⊢ runtime runtime-env γ⊢ L-image L⊢)
  interpret-typing (suc n) W⊢ runtime runtime-env γ⊢
      (primitive-term addℕ L-image M-image)
      (N.⊢⊕ L⊢ addℕ M⊢)
      | timed W₁ | timeout-typed W≤W₁
      rewrite L-eq =
    timeout-typed W≤W₁
  interpret-typing (suc n) W⊢ runtime runtime-env γ⊢
      (primitive-term addℕ L-image M-image)
      (N.⊢⊕ L⊢ addℕ M⊢)
      | blamed W₁ | blame-typed W≤W₁
      rewrite L-eq =
    blame-typed W≤W₁
  interpret-typing (suc n) W⊢ runtime runtime-env γ⊢
      (primitive-term addℕ L-image M-image)
      (N.⊢⊕ L⊢ addℕ M⊢)
      | failed W₁ e | ()
  interpret-typing (suc n) W⊢ runtime runtime-env γ⊢
      (primitive-term addℕ L-image M-image)
      (N.⊢⊕ L⊢ addℕ M⊢)
      | returned W₁ (constant (κℕ k))
      | return-typed W≤W₁ W₁⊢ constant-typed
      rewrite L-eq
      with interpret W₁ _ _ _ n in M-eq
  interpret-typing (suc n) W⊢ runtime runtime-env γ⊢
      (primitive-term addℕ L-image M-image)
      (N.⊢⊕ L⊢ addℕ M⊢)
      | returned W₁ (constant (κℕ k))
      | return-typed W≤W₁ W₁⊢ constant-typed
      | M-result
      with subst (OutcomeTyping _ _) M-eq
        (interpret-typing n W₁⊢
          (runtime-context-weaken W≤W₁ runtime)
          runtime-env
          (environment-weaken W≤W₁ W₁⊢ γ⊢)
          M-image M⊢)
  interpret-typing (suc n) W⊢ runtime runtime-env γ⊢
      (primitive-term addℕ L-image M-image)
      (N.⊢⊕ L⊢ addℕ M⊢)
      | returned W₁ (constant (κℕ k))
      | return-typed W≤W₁ W₁⊢ constant-typed
      | timed W₂ | timeout-typed W₁≤W₂
      rewrite M-eq =
    timeout-typed (world-extension-trans W≤W₁ W₁≤W₂)
  interpret-typing (suc n) W⊢ runtime runtime-env γ⊢
      (primitive-term addℕ L-image M-image)
      (N.⊢⊕ L⊢ addℕ M⊢)
      | returned W₁ (constant (κℕ k))
      | return-typed W≤W₁ W₁⊢ constant-typed
      | blamed W₂ | blame-typed W₁≤W₂
      rewrite M-eq =
    blame-typed (world-extension-trans W≤W₁ W₁≤W₂)
  interpret-typing (suc n) W⊢ runtime runtime-env γ⊢
      (primitive-term addℕ L-image M-image)
      (N.⊢⊕ L⊢ addℕ M⊢)
      | returned W₁ (constant (κℕ k))
      | return-typed W≤W₁ W₁⊢ constant-typed
      | failed W₂ e | ()
  interpret-typing (suc n) W⊢ runtime runtime-env γ⊢
      (primitive-term addℕ L-image M-image)
      (N.⊢⊕ L⊢ addℕ M⊢)
      | returned W₁ (constant (κℕ k))
      | return-typed W≤W₁ W₁⊢ constant-typed
      | returned W₂ (constant (κℕ j))
      | return-typed W₁≤W₂ W₂⊢ constant-typed
      rewrite M-eq =
    return-typed
      (world-extension-trans W≤W₁ W₁≤W₂)
      W₂⊢ constant-typed

  interpret-typing (suc n) W⊢ runtime runtime-env γ⊢
      (coercion-application-term M-image)
      (N.⊢⟨⟩ c⊢ M⊢)
      with interpret _ _ _ _ n in M-eq
  interpret-typing (suc n) W⊢ runtime runtime-env γ⊢
      (coercion-application-term M-image)
      (N.⊢⟨⟩ c⊢ M⊢)
      | M-result
      with subst (OutcomeTyping _ _) M-eq
        (interpret-typing n W⊢ runtime runtime-env γ⊢ M-image M⊢)
  interpret-typing (suc n) W⊢ runtime runtime-env γ⊢
      (coercion-application-term M-image)
      (N.⊢⟨⟩ c⊢ M⊢)
      | timed W₁ | timeout-typed W≤W₁
      rewrite M-eq =
    timeout-typed W≤W₁
  interpret-typing (suc n) W⊢ runtime runtime-env γ⊢
      (coercion-application-term M-image)
      (N.⊢⟨⟩ c⊢ M⊢)
      | blamed W₁ | blame-typed W≤W₁
      rewrite M-eq =
    blame-typed W≤W₁
  interpret-typing (suc n) W⊢ runtime runtime-env γ⊢
      (coercion-application-term M-image)
      (N.⊢⟨⟩ c⊢ M⊢)
      | failed W₁ e | ()
  interpret-typing (suc n) W⊢ runtime runtime-env γ⊢
      (coercion-application-term M-image)
      (N.⊢⟨⟩ c⊢ M⊢)
      | returned W₁ V | return-typed W≤W₁ W₁⊢ V⊢
      rewrite M-eq =
    outcome-rebase W≤W₁
      (coerceValue-typing n W₁⊢
        (runtime-context-weaken W≤W₁ runtime)
        runtime-env
        c⊢ V⊢)

  ----------------------------------------------------------------------
  -- Function application
  ----------------------------------------------------------------------

  applyValue-typing zero W⊢ V⊢ U⊢ =
    timeout-typed world-extension-refl

  applyValue-typing (suc n) W⊢
      (closure-typed closure-W⊢ runtime runtime-env γ⊢ image body⊢)
      U⊢ =
    interpret-typing n W⊢ runtime
      runtime-env
      (environment-cons U⊢ γ⊢) image body⊢

  applyValue-typing (suc n) W⊢
      (function-proxy-typed proxy-W⊢ runtime runtime-env γ⊢
        (cast-fun p⊢ q⊢) V⊢)
      U⊢
      with coerceValue _ _ _ _ n in p-eq
  applyValue-typing (suc n) W⊢
      (function-proxy-typed proxy-W⊢ runtime runtime-env γ⊢
        (cast-fun p⊢ q⊢) V⊢)
      U⊢
      | p-result
      with subst (OutcomeTyping _ _) p-eq
        (coerceValue-typing n W⊢ runtime runtime-env p⊢ U⊢)
  applyValue-typing (suc n) W⊢
      (function-proxy-typed proxy-W⊢ runtime runtime-env γ⊢
        (cast-fun p⊢ q⊢) V⊢)
      U⊢
      | timed W₁ | timeout-typed W≤W₁
      rewrite p-eq =
    timeout-typed W≤W₁
  applyValue-typing (suc n) W⊢
      (function-proxy-typed proxy-W⊢ runtime runtime-env γ⊢
        (cast-fun p⊢ q⊢) V⊢)
      U⊢
      | blamed W₁ | blame-typed W≤W₁
      rewrite p-eq =
    blame-typed W≤W₁
  applyValue-typing (suc n) W⊢
      (function-proxy-typed proxy-W⊢ runtime runtime-env γ⊢
        (cast-fun p⊢ q⊢) V⊢)
      U⊢
      | failed W₁ e | ()
  applyValue-typing (suc n) W⊢
      (function-proxy-typed proxy-W⊢ runtime runtime-env γ⊢
        (cast-fun p⊢ q⊢) V⊢)
      U⊢
      | returned W₁ U′ | return-typed W≤W₁ W₁⊢ U′⊢
      rewrite p-eq
      with applyValue W₁ _ _ n in apply-eq
  applyValue-typing (suc n) W⊢
      (function-proxy-typed proxy-W⊢ runtime runtime-env γ⊢
        (cast-fun p⊢ q⊢) V⊢)
      U⊢
      | returned W₁ U′ | return-typed W≤W₁ W₁⊢ U′⊢
      | apply-result
      with subst (OutcomeTyping _ _) apply-eq
        (applyValue-typing n W₁⊢
          (value-weaken W≤W₁ W₁⊢ V⊢) U′⊢)
  applyValue-typing (suc n) W⊢
      (function-proxy-typed proxy-W⊢ runtime runtime-env γ⊢
        (cast-fun p⊢ q⊢) V⊢)
      U⊢
      | returned W₁ U′ | return-typed W≤W₁ W₁⊢ U′⊢
      | timed W₂ | timeout-typed W₁≤W₂
      rewrite apply-eq =
    timeout-typed (world-extension-trans W≤W₁ W₁≤W₂)
  applyValue-typing (suc n) W⊢
      (function-proxy-typed proxy-W⊢ runtime runtime-env γ⊢
        (cast-fun p⊢ q⊢) V⊢)
      U⊢
      | returned W₁ U′ | return-typed W≤W₁ W₁⊢ U′⊢
      | blamed W₂ | blame-typed W₁≤W₂
      rewrite apply-eq =
    blame-typed (world-extension-trans W≤W₁ W₁≤W₂)
  applyValue-typing (suc n) W⊢
      (function-proxy-typed proxy-W⊢ runtime runtime-env γ⊢
        (cast-fun p⊢ q⊢) V⊢)
      U⊢
      | returned W₁ U′ | return-typed W≤W₁ W₁⊢ U′⊢
      | failed W₂ e | ()
  applyValue-typing (suc n) W⊢
      (function-proxy-typed proxy-W⊢ runtime runtime-env γ⊢
        (cast-fun p⊢ q⊢) V⊢)
      U⊢
      | returned W₁ U′ | return-typed W≤W₁ W₁⊢ U′⊢
      | returned W₂ V′ | return-typed W₁≤W₂ W₂⊢ V′⊢
      rewrite apply-eq =
    outcome-rebase
      (world-extension-trans W≤W₁ W₁≤W₂)
      (coerceValue-typing n W₂⊢
        (runtime-context-weaken
          (world-extension-trans W≤W₁ W₁≤W₂) runtime)
        runtime-env
        q⊢ V′⊢)

  ----------------------------------------------------------------------
  -- Polymorphic instantiation
  ----------------------------------------------------------------------

  instantiateValue-typing zero W⊢ α-ok V⊢ =
    timeout-typed world-extension-refl

  instantiateValue-typing (suc n) {α = α} W⊢ α-ok
      (type-abstraction-typed {Δ = Δ} {Σ} {Γ}
        {θ} {γ} {X} {V = V} {A = A} {P = P} {vP = vP}
        abstraction-W⊢ runtime runtime-env γ⊢
        fresh closed image body⊢) =
    outcome-type-transport
      (sym (instantiate-interpret
        (nominal-type (seal-name α)) θ A))
      (return-typed world-extension-refl W⊢
        (substituteName-closedValue-typing W⊢
          (runtime-context-name (seal-scoped α-ok)
            (runtime-context-weaken world-extension-refl runtime))
          (runtime-type-seal runtime-env)
          (environment-type-weaken
            (seal-name α) γ⊢)
          image body⊢
          (here refl) (replaceName-head fresh) closed))

  instantiateValue-typing (suc n) {α = α} W⊢ α-ok
      (forall-proxy-typed {θ = θ} {A = A} {B = B}
        proxy-W⊢ runtime runtime-env γ⊢
        (cast-all c⊢) V⊢)
      with instantiateValue _ _ _ n in inst-eq
  instantiateValue-typing (suc n) {α = α} W⊢ α-ok
      (forall-proxy-typed {θ = θ} {A = A} {B = B}
        proxy-W⊢ runtime runtime-env γ⊢
        (cast-all c⊢) V⊢)
      | inst-result
      with subst (OutcomeTyping _ _) inst-eq
        (instantiateValue-typing n W⊢ α-ok V⊢)
  instantiateValue-typing (suc n) {α = α} W⊢ α-ok
      (forall-proxy-typed {θ = θ} {A = A} {B = B}
        proxy-W⊢ runtime runtime-env γ⊢
        (cast-all c⊢) V⊢)
      | timed W₁ | timeout-typed W≤W₁
      rewrite inst-eq =
    timeout-typed W≤W₁
  instantiateValue-typing (suc n) {α = α} W⊢ α-ok
      (forall-proxy-typed {θ = θ} {A = A} {B = B}
        proxy-W⊢ runtime runtime-env γ⊢
        (cast-all c⊢) V⊢)
      | blamed W₁ | blame-typed W≤W₁
      rewrite inst-eq =
    blame-typed W≤W₁
  instantiateValue-typing (suc n) {α = α} W⊢ α-ok
      (forall-proxy-typed {θ = θ} {A = A} {B = B}
        proxy-W⊢ runtime runtime-env γ⊢
        (cast-all c⊢) V⊢)
      | failed W₁ e | ()
  instantiateValue-typing (suc n) {α = α} W⊢ α-ok
      (forall-proxy-typed {θ = θ} {A = A} {B = B}
        proxy-W⊢ runtime runtime-env γ⊢
        (cast-all c⊢) V⊢)
      | returned W₁ U | return-typed W≤W₁ W₁⊢ U⊢
      rewrite inst-eq =
    outcome-type-transport
      (sym (instantiate-interpret
        (nominal-type (seal-name α)) θ B))
      (outcome-rebase W≤W₁
        (coerceValue-typing n W₁⊢
          (runtime-context-name
            (seal-scoped (allocated-weaken W≤W₁ α-ok))
            (runtime-context-weaken W≤W₁ runtime))
          (runtime-type-seal runtime-env)
          c⊢
          (subst (ValueTyping W₁ U)
            (instantiate-interpret
              (nominal-type (seal-name α)) θ A)
            U⊢)))

  instantiateValue-typing (suc n) {α = α} W⊢ α-ok
      (generalized-typed {θ = θ} {A = A} {B = B}
        generalized-W⊢ runtime runtime-env γ⊢
        (cast-gen hA occurs c⊢) V⊢) =
    outcome-type-transport
      (sym (instantiate-interpret
        (nominal-type (seal-name α)) θ B))
      (coerceValue-typing n W⊢
        (runtime-context-name (seal-scoped α-ok) runtime)
        (runtime-type-seal runtime-env)
        c⊢
        (subst (ValueTyping _ _)
          (sym (interpret-weaken
            (nominal-type (seal-name α))
            (semanticEnvironment θ) A))
          V⊢))

  ----------------------------------------------------------------------
  -- Coercion interpretation
  ----------------------------------------------------------------------

  coerceValue-typing zero W⊢ runtime runtime-env c⊢ V⊢ =
    timeout-typed world-extension-refl

  coerceValue-typing (suc n) W⊢ runtime runtime-env
      (cast-id hA allowed) V⊢ =
    return-typed world-extension-refl W⊢ V⊢

  coerceValue-typing (suc n) W⊢ runtime runtime-env
      (cast-seq c⊢ d⊢) V⊢
      with coerceValue _ _ _ _ n in c-eq
  coerceValue-typing (suc n) W⊢ runtime runtime-env
      (cast-seq c⊢ d⊢) V⊢
      | c-result
      with subst (OutcomeTyping _ _) c-eq
        (coerceValue-typing n W⊢ runtime runtime-env c⊢ V⊢)
  coerceValue-typing (suc n) W⊢ runtime runtime-env
      (cast-seq c⊢ d⊢) V⊢
      | timed W₁ | timeout-typed W≤W₁
      rewrite c-eq =
    timeout-typed W≤W₁
  coerceValue-typing (suc n) W⊢ runtime runtime-env
      (cast-seq c⊢ d⊢) V⊢
      | blamed W₁ | blame-typed W≤W₁
      rewrite c-eq =
    blame-typed W≤W₁
  coerceValue-typing (suc n) W⊢ runtime runtime-env
      (cast-seq c⊢ d⊢) V⊢
      | failed W₁ e | ()
  coerceValue-typing (suc n) W⊢ runtime runtime-env
      (cast-seq c⊢ d⊢) V⊢
      | returned W₁ U | return-typed W≤W₁ W₁⊢ U⊢
      rewrite c-eq =
    outcome-rebase W≤W₁
      (coerceValue-typing n W₁⊢
        (runtime-context-weaken W≤W₁ runtime)
        runtime-env
        d⊢ U⊢)

  coerceValue-typing (suc n) W⊢ runtime runtime-env
      c⊢@(cast-fun p⊢ q⊢) V⊢ =
    return-typed world-extension-refl W⊢
      (function-proxy-typed W⊢ runtime runtime-env
        environment-empty c⊢ V⊢)

  coerceValue-typing (suc n) W⊢ runtime runtime-env
      c⊢@(cast-all body⊢) V⊢ =
    return-typed world-extension-refl W⊢
      (forall-proxy-typed W⊢ runtime runtime-env
        environment-empty c⊢ V⊢)

  coerceValue-typing (suc n) W⊢ runtime runtime-env
      c⊢@(cast-tag hG gG allowed) V⊢
      with ground?-complete
        (runtime-ground-from-typing runtime-env runtime hG gG)
  coerceValue-typing (suc n) W⊢ runtime runtime-env
      c⊢@(cast-tag hG gG allowed) V⊢
      | gG′ , ground-eq
      rewrite ground-eq =
    return-typed world-extension-refl W⊢
      (tagged-typed W⊢ runtime gG′
        environment-empty c⊢ V⊢)

  coerceValue-typing (suc n) W⊢ runtime runtime-env
      (cast-untag hG gG allowed)
      (tagged-typed {gG = gH}
        tagged-W⊢ tagged-runtime tagged-runtime-ground tagged-env
        (cast-tag hH gH′ tag-allowed) V⊢)
      with ground?-complete
        (runtime-ground-from-typing runtime-env runtime hG gG)
  coerceValue-typing (suc n) W⊢ runtime runtime-env
      (cast-untag hG gG allowed)
      (tagged-typed {gG = gH}
        tagged-W⊢ tagged-runtime tagged-runtime-ground tagged-env
        (cast-tag hH gH′ tag-allowed) V⊢)
      | gG′ , ground-eq
      rewrite ground-eq
      with tagOf-complete runtime hG
           (runtime-ground-syntax gG′)
         | tagOf-complete tagged-runtime hH gH
  coerceValue-typing (suc n) W⊢ runtime runtime-env
      (cast-untag hG gG allowed)
      (tagged-typed {gG = gH}
        tagged-W⊢ tagged-runtime tagged-runtime-ground tagged-env
        (cast-tag hH gH′ tag-allowed) V⊢)
      | gG′ , ground-eq | expected , expected-eq
      | actual , actual-eq
      rewrite expected-eq | actual-eq
      with expected ≟Tag actual
  coerceValue-typing (suc n) W⊢ runtime runtime-env
      (cast-untag hG gG allowed)
      (tagged-typed {gG = gH}
        tagged-W⊢ tagged-runtime tagged-runtime-ground tagged-env
        (cast-tag hH gH′ tag-allowed) V⊢)
      | gG′ , ground-eq | expected , expected-eq
      | .expected , actual-eq | yes refl =
    return-typed world-extension-refl W⊢
      (subst (ValueTyping _ _)
        (sym (matching-tags-type-eq
          (runtime-ground-syntax gG′) gH
          expected-eq actual-eq))
        V⊢)
  coerceValue-typing (suc n) W⊢ runtime runtime-env
      (cast-untag hG gG allowed)
      (tagged-typed {gG = gH}
        tagged-W⊢ tagged-runtime tagged-runtime-ground tagged-env
        (cast-tag hH gH′ tag-allowed) V⊢)
      | gG′ , ground-eq | expected , expected-eq
      | actual , actual-eq | no expected≢actual =
    blame-typed world-extension-refl

  coerceValue-typing (suc n) {θ = θ} W⊢ runtime runtime-env
      c⊢@(cast-seal {α = X} hA X∈ allowed) V⊢
      with store-lookup-sound (store-typing runtime) X∈
  coerceValue-typing (suc n) {θ = θ} W⊢ runtime runtime-env
      c⊢@(cast-seal {α = X} hA X∈ allowed) V⊢
      | α , name-eq , representation
      rewrite name-eq =
    outcome-type-transport
      (sym (semantic-name-lookup
        {θ = θ} {X = X} name-eq))
      (return-typed world-extension-refl W⊢
        (sealed-typed W⊢ runtime environment-empty
          c⊢ name-eq representation V⊢))

  coerceValue-typing (suc n) {θ = θ} W⊢ runtime runtime-env
      (cast-unseal {α = X} hA X∈ allowed) V⊢
      with store-lookup-sound (store-typing runtime) X∈
  coerceValue-typing (suc n) {θ = θ} W⊢ runtime runtime-env
      (cast-unseal {α = X} hA X∈ allowed) V⊢
      | α , name-eq , representation
      rewrite name-eq
      with subst (ValueTyping _ _)
        (semantic-name-lookup
          {θ = θ} {X = X} name-eq) V⊢
  coerceValue-typing (suc n) W⊢ runtime runtime-env
      (cast-unseal hA X∈ allowed) V⊢
      | α , name-eq , representation
      | sealed-typed sealed-W⊢ sealed-runtime sealed-env
          sealed-c⊢ sealed-name-eq sealed-representation U⊢
      with α ≟SealName α
  coerceValue-typing (suc n) W⊢ runtime runtime-env
      (cast-unseal hA X∈ allowed) V⊢
      | α , name-eq , representation
      | sealed-typed sealed-W⊢ sealed-runtime sealed-env
          sealed-c⊢ sealed-name-eq sealed-representation U⊢
      | yes refl =
    return-typed world-extension-refl W⊢
      (subst (ValueTyping _ _)
        (representation-functional W⊢
          sealed-representation representation)
        U⊢)
  coerceValue-typing (suc n) W⊢ runtime runtime-env
      (cast-unseal hA X∈ allowed) V⊢
      | α , name-eq , representation
      | sealed-typed sealed-W⊢ sealed-runtime sealed-env
          sealed-c⊢ sealed-name-eq sealed-representation U⊢
      | no α≢α =
    ⊥-elim (α≢α refl)

  coerceValue-typing (suc n) W⊢ runtime runtime-env
      c⊢@(cast-gen hA occurs body⊢) V⊢ =
    return-typed world-extension-refl W⊢
      (generalized-typed W⊢ runtime runtime-env
        environment-empty c⊢ V⊢)

  coerceValue-typing (suc n) {W = W} {θ = θ}
      W⊢ runtime runtime-env
      (cast-inst {A = A} {B = B} hB occurs c⊢) V⊢
      with instantiateValue
        (allocate W ★ θ) (freshSealName W) _ n in inst-eq
  coerceValue-typing (suc n) {W = W} {θ = θ}
      W⊢ runtime runtime-env
      (cast-inst {A = A} {B = B} hB occurs c⊢) V⊢
      | inst-result
      with subst (OutcomeTyping _ _) inst-eq
        (instantiateValue-typing n
          (allocate-world-typed W⊢ runtime wf★)
          allocated-here
          (value-weaken
            (world-extension-allocate world-extension-refl)
            (allocate-world-typed W⊢ runtime wf★)
            V⊢))
  coerceValue-typing (suc n) {W = W} {θ = θ}
      W⊢ runtime runtime-env
      (cast-inst {A = A} {B = B} hB occurs c⊢) V⊢
      | timed W₁ | timeout-typed W⁺≤W₁
      rewrite inst-eq =
    timeout-typed
      (world-extension-trans
        (world-extension-allocate world-extension-refl)
        W⁺≤W₁)
  coerceValue-typing (suc n) {W = W} {θ = θ}
      W⊢ runtime runtime-env
      (cast-inst {A = A} {B = B} hB occurs c⊢) V⊢
      | blamed W₁ | blame-typed W⁺≤W₁
      rewrite inst-eq =
    blame-typed
      (world-extension-trans
        (world-extension-allocate world-extension-refl)
        W⁺≤W₁)
  coerceValue-typing (suc n) {W = W} {θ = θ}
      W⊢ runtime runtime-env
      (cast-inst {A = A} {B = B} hB occurs c⊢) V⊢
      | failed W₁ e | ()
  coerceValue-typing (suc n) {W = W} {θ = θ}
      W⊢ runtime runtime-env
      (cast-inst {A = A} {B = B} hB occurs c⊢) V⊢
      | returned W₁ U | return-typed W⁺≤W₁ W₁⊢ U⊢
      rewrite inst-eq =
    outcome-type-transport
      (interpret-weaken
        (nominal-type (seal-name (freshSealName W)))
        (semanticEnvironment θ) B)
      (outcome-rebase
        (world-extension-trans
          (world-extension-allocate world-extension-refl)
          W⁺≤W₁)
        (coerceValue-typing n W₁⊢
          (runtime-context-weaken W⁺≤W₁
            (runtime-context-seal runtime))
          (runtime-type-seal runtime-env)
          c⊢
          (subst (ValueTyping W₁ U)
            (instantiate-interpret
              (nominal-type
                (seal-name (freshSealName W)))
              θ A)
            U⊢)))

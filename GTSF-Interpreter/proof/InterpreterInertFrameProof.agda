module proof.InterpreterInertFrameProof where

-- File Charter:
--   * Proves that every well-typed inert coercion constructs its explicit
--     runtime wrapper in one positive interpreter index.
--   * Resolves tag and seal lookups from unary runtime typing.
--   * Contains no term interpretation or reduction result.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Coercions using (Inert; _∣_∣_⊢_∶_=⇒_)
import Coercions as C
open import Data.Product using (_,_)
import Data.Maybe
import Data.Nat

open import Interpreter
open import Runtime.InterpreterClosedValueFrame
open import Simulation.Coercion.InterpreterCoercionComputation using
  ( coerce-forall-computation
  ; coerce-function-computation
  ; coerce-generalization-computation
  ; coerce-tag-computation
  )
open import Runtime.InterpreterInertFrameCore
open import Typing.InterpreterSemanticTypingCore
open import proof.InterpreterCoercionTyping using
  (ground?-complete; runtime-ground-from-typing; tagOf-complete)
open import proof.InterpreterSemanticTypingProperties using
  (store-lookup-sound)

seal-frame-computes :
  ∀ {W θ A X V α} →
  lookup θ X ≡ Data.Maybe.just (seal-name α) →
  ∀ n →
  coerceValue W θ (C.seal A X) V
    (Data.Nat.suc n) ≡ returned W (sealed α V)
seal-frame-computes lookup-eq n rewrite lookup-eq =
  refl

execute-inert-frame :
  ∀ {W Δ Σ θ μ c A B V}
    (runtime : RuntimeContext W Δ Σ θ)
    (runtime-env : RuntimeTypeEnvironment θ)
    (typing : μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B)
    (inert : Inert c) →
  InertFrameExecution W θ c V inert
execute-inert-frame runtime runtime-env
    (C.cast-tag hG gG allowed) (G C.!)
    with ground?-complete
      (runtime-ground-from-typing runtime-env runtime hG gG)
execute-inert-frame runtime runtime-env
    (C.cast-tag hG gG allowed) (G C.!)
    | runtime-ground , ground-eq
    with tagOf-complete runtime hG
      (runtime-ground-syntax runtime-ground)
execute-inert-frame runtime runtime-env
    (C.cast-tag hG gG allowed) (G C.!)
    | runtime-ground , ground-eq | tag , tag-eq =
  inert-frame-execution
    (tagged (runtime-ground-syntax runtime-ground) _ _)
    closed-tag-frame
    λ n → coerce-tag-computation ground-eq tag-eq (Data.Nat.suc n)
execute-inert-frame {W = W} {θ = θ} {V = V} runtime runtime-env
    (C.cast-seal hA X∈Σ allowed) (C.seal A X)
    with store-lookup-sound (store-typing runtime) X∈Σ
execute-inert-frame {W = W} {θ = θ} {V = V} runtime runtime-env
    (C.cast-seal hA X∈Σ allowed) (C.seal A X)
    | α , lookup-eq , representation =
  inert-frame-execution
    (sealed α _)
    (closed-seal-frame lookup-eq)
    (seal-frame-computes
      {W = W} {θ = θ} {A = A} {X = X} {V = V} {α = α}
      lookup-eq)
execute-inert-frame runtime runtime-env
    (C.cast-fun p⊢ q⊢) (p C.↦ q) =
  inert-frame-execution
    (function-proxy p q _ _)
    closed-function-frame
    λ n → coerce-function-computation (Data.Nat.suc n)
execute-inert-frame runtime runtime-env
    (C.cast-all c⊢) (C.`∀ c) =
  inert-frame-execution
    (forall-proxy c _ _)
    closed-forall-frame
    λ n → coerce-forall-computation (Data.Nat.suc n)
execute-inert-frame runtime runtime-env
    (C.cast-gen hA occ c⊢) (C.gen A c) =
  inert-frame-execution
    (generalized A c _ _)
    closed-generalized-frame
    λ n → coerce-generalization-computation (Data.Nat.suc n)

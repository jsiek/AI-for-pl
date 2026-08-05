module InterpreterAdequacy.proof.ImmediateCoercionBlameCompleteness where

-- File Charter:
--   * Converts positive-fuel termination of one active coercion into a finite
--     blamed interpreter run when the supplied small-step trace ends in blame.
--   * Excludes a returned value by return soundness and terminal determinism.
--   * Constructs no reduction step and makes no convergence assumption.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([])
open import Data.Nat using (suc; zero)
open import Data.Product using (_,_; Σ-syntax)

import Coercions as C
open import Interpreter
open import InterpreterAdequacy.TraceAgreement
open import InterpreterAdequacy.proof.ReturnTrace using
  (return-trace)
open import InterpreterAdequacy.proof.RunReturnSoundnessProof using
  (coerce-return-soundᵢ)
open import InterpreterAdequacy.proof.TraceAgreementProperties using
  (value-trace-value)
open import Typing.InterpreterCoercionSemanticTyping using
  (coerceValue-never-fails)
open import Typing.InterpreterSemanticTypingCore
open import NuReduction using (_—↠[_]_)
import NuTerms as N
open import proof.DGG.Core.NuReductionDeterminism using
  (source-blame-excludes-value)

complete-immediate-coercion-blame :
  ∀ {W prefix Δ Σ θ τ c V u A B μ changes} →
  (world-agreement : WorldTraceAgreement W prefix) →
  (W⊢ : WorldTyping W) →
  (runtime : RuntimeContext W Δ Σ θ) →
  (runtime-env : RuntimeTypeEnvironment θ) →
  C._∣_∣_⊢_∶_=⇒_ μ Δ Σ c A B →
  ValueTyping W V ⟦ A ⟧[ θ ] →
  TypeEnvironmentTraceAgreement world-agreement [] θ τ →
  ValueTraceAgreement world-agreement [] V u →
  (u N.⟨ C.renameᶜ τ c ⟩) —↠[ changes ] N.blame →
  (∀ {Z} → coerceValue W θ c V (suc zero) ≡ timed Z → ⊥) →
  Σ[ Z ∈ World ] coerceValue W θ c V (suc zero) ≡ blamed Z
complete-immediate-coercion-blame {W = W} {θ = θ} {c = c} {V = V}
    world-agreement W⊢ runtime runtime-env c⊢ V⊢ θ-agrees V-agrees
    trace not-timed with coerceValue W θ c V (suc zero) in result-eq
complete-immediate-coercion-blame world-agreement W⊢ runtime runtime-env
    c⊢ V⊢ θ-agrees V-agrees trace not-timed | timed Z =
  ⊥-elim (not-timed refl)
complete-immediate-coercion-blame world-agreement W⊢ runtime runtime-env
    c⊢ V⊢ θ-agrees V-agrees trace not-timed | blamed Z =
  Z , refl
complete-immediate-coercion-blame world-agreement W⊢ runtime runtime-env
    c⊢ V⊢ θ-agrees V-agrees trace not-timed | failed Z e =
  ⊥-elim
    (coerceValue-never-fails (suc zero) W⊢ runtime runtime-env
      c⊢ V⊢ result-eq)
complete-immediate-coercion-blame world-agreement W⊢ runtime runtime-env
    c⊢ V⊢ θ-agrees V-agrees trace not-timed | returned Z R
    with coerce-return-soundᵢ (suc zero) world-agreement
      θ-agrees V-agrees result-eq
complete-immediate-coercion-blame world-agreement W⊢ runtime runtime-env
    c⊢ V⊢ θ-agrees V-agrees trace not-timed | returned Z R
    | return-trace return-changes v path reduction R-agrees =
  ⊥-elim
    (source-blame-excludes-value trace reduction
      (value-trace-value R-agrees))

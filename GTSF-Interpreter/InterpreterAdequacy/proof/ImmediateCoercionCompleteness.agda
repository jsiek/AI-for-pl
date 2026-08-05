module InterpreterAdequacy.proof.ImmediateCoercionCompleteness where

-- File Charter:
--   * Converts positive-fuel termination of one active coercion into a finite
--     successful interpreter return when the supplied small-step trace ends
--     in a value.
--   * Excludes blame by determinism against that concrete terminating trace
--     and excludes errors by semantic typing.
--   * Constructs no reduction step and makes no convergence assumption.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([])
open import Data.Nat using (suc; zero)
open import Data.Product using (_,_; Σ-syntax)

import Coercions as C
open import Interpreter
open import InterpreterAdequacy.TraceAgreement
open import InterpreterAdequacy.proof.BlameTrace using
  (blame-trace)
open import InterpreterAdequacy.proof.RunBlameSoundnessProof using
  (coerce-blame-soundᵢ)
open import Typing.InterpreterCoercionSemanticTyping using
  (coerceValue-never-fails)
open import Typing.InterpreterSemanticTypingCore
open import NuReduction using (_—↠[_]_)
import NuTerms as N
open import proof.DGG.Core.NuReductionDeterminism using
  (source-blame-excludes-value)

complete-immediate-coercion :
  ∀ {W prefix Δ Σ θ τ c V u A B μ changes v} →
  (world-agreement : WorldTraceAgreement W prefix) →
  (W⊢ : WorldTyping W) →
  (runtime : RuntimeContext W Δ Σ θ) →
  (runtime-env : RuntimeTypeEnvironment θ) →
  C._∣_∣_⊢_∶_=⇒_ μ Δ Σ c A B →
  ValueTyping W V ⟦ A ⟧[ θ ] →
  TypeEnvironmentTraceAgreement world-agreement [] θ τ →
  ValueTraceAgreement world-agreement [] V u →
  (u N.⟨ C.renameᶜ τ c ⟩) —↠[ changes ] v →
  N.Value v →
  (∀ {Z} → coerceValue W θ c V (suc zero) ≡ timed Z → ⊥) →
  Σ[ n ∈ StepIndex ]
  Σ[ Z ∈ World ]
  Σ[ R ∈ Value ] coerceValue W θ c V n ≡ returned Z R
complete-immediate-coercion {W = W} {θ = θ} {c = c} {V = V}
    world-agreement W⊢ runtime runtime-env c⊢ V⊢ θ-agrees V-agrees
    trace vV not-timed with coerceValue W θ c V (suc zero) in result-eq
complete-immediate-coercion world-agreement W⊢ runtime runtime-env
    c⊢ V⊢ θ-agrees V-agrees trace vV not-timed
    | timed Z =
  ⊥-elim (not-timed Agda.Builtin.Equality.refl)
complete-immediate-coercion world-agreement W⊢ runtime runtime-env
    c⊢ V⊢ θ-agrees V-agrees trace vV not-timed
    | blamed Z
    with coerce-blame-soundᵢ (suc zero) world-agreement
      θ-agrees V-agrees result-eq
complete-immediate-coercion world-agreement W⊢ runtime runtime-env
    c⊢ V⊢ θ-agrees V-agrees trace vV not-timed
    | blamed Z | blame-trace blame-changes path blame-reduction =
  ⊥-elim (source-blame-excludes-value blame-reduction trace vV)
complete-immediate-coercion world-agreement W⊢ runtime runtime-env
    c⊢ V⊢ θ-agrees V-agrees trace vV not-timed
    | failed Z e =
  ⊥-elim
    (coerceValue-never-fails (suc zero) W⊢ runtime runtime-env
      c⊢ V⊢ result-eq)
complete-immediate-coercion world-agreement W⊢ runtime runtime-env
    c⊢ V⊢ θ-agrees V-agrees trace vV not-timed
    | returned Z R =
  suc zero , Z , R , result-eq

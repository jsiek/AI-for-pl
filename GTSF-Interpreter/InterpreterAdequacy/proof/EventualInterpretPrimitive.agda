module InterpreterAdequacy.proof.EventualInterpretPrimitive where

-- File Charter:
--   * Constructs a finite interpreter return for a terminating primitive
--     application by synchronizing its two operand phases.
--   * Uses semantic base-type canonical forms to discharge the final
--     primitive computation explicitly.
--   * Receives recursive completeness only through `StrictlySmallerSolver`.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_; length)
open import Data.Nat using (_+_; _<_; suc)
open import Data.Product using (_,_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (subst)

open import Interpreter
open import InterpreterAdequacy.TraceAgreement
open import InterpreterAdequacy.proof.EventualReturnAlignment using
  (align-interpret-return)
open import InterpreterAdequacy.proof.EventualReturnProblem
open import InterpreterAdequacy.proof.EventualReturnTyping using
  (interpret-returned-typing)
open import InterpreterAdequacy.proof.FiniteRunComposition using
  (interpret-primitive-from-phases)
open import InterpreterAdequacy.proof.PrimitiveTraceDecomposition
open import InterpreterAdequacy.proof.TraceAgreementPath using
  (term-trace-path-empty; value-trace-path-empty)
open import InterpreterAdequacy.proof.TraceAgreementProperties using
  (world-trace-agreement-++)
open import InterpreterAdequacy.proof.TraceMeasure using
  (left-before-right-step-shorter; middle-before-step-shorter)
open import Typing.InterpreterSemanticTypingCore
open import SmallStepInterface.InterpreterTermShape using (InterpreterTerm)
open import NuReduction
import NuTerms as N
open import Primitives using (addℕ)
open import proof.InterpreterSemanticTypingProperties using
  (environment-weaken; runtime-context-weaken; value-weaken)
open import InterpreterAdequacy.proof.InterpreterTermNoBullet using
  (interpreter-term-no-bullet)
open import Types using (`ℕ; ‵_)

complete-interpret-primitive :
  ∀ {measure W prefix Δ Σ Γ γ θ L M P changes v} →
  StrictlySmallerSolver measure →
  length changes ≡ measure →
  (world-agreement : WorldTraceAgreement W prefix) →
  (W⊢ : WorldTyping W) →
  (runtime : RuntimeContext W Δ Σ θ) →
  (runtime-env : RuntimeTypeEnvironment θ) →
  (environment : EnvironmentTyping W θ γ Γ) →
  (L-image : InterpreterTerm L) →
  (M-image : InterpreterTerm M) →
  N._∣_∣_⊢_⦂_ Δ Σ Γ L (‵ `ℕ) →
  N._∣_∣_⊢_⦂_ Δ Σ Γ M (‵ `ℕ) →
  TermTraceAgreement world-agreement [] γ θ
    (L N.⊕[ addℕ ] M) P →
  P —↠[ changes ] v →
  N.Value v →
  Σ[ n ∈ StepIndex ]
  Σ[ Z ∈ World ]
  Σ[ R ∈ Value ]
    interpret W γ θ (L N.⊕[ addℕ ] M) n ≡ returned Z R
complete-interpret-primitive solver measure-eq world-agreement W⊢
    runtime runtime-env environment L-image M-image L⊢ M⊢
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace vV
    with decompose-primitive-value-trace trace′ vV
  where
  trace′ = subst (\ Q → Q —↠[ _ ] _)
    reification trace
complete-interpret-primitive solver measure-eq world-agreement W⊢
    runtime runtime-env environment L-image M-image L⊢ M⊢
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace vV
    | primitive-trace-decomposition
        changes-L changes-M (change ∷ changes-A) f u vf vu
        L-trace M-trace (↠-step root active-tail) refl
    with solver L-smaller
      (interpret-problem refl world-agreement W⊢ runtime runtime-env
        environment L-image L⊢ L-agrees L-trace vf)
  where
  L-agrees = term-trace-agreement τ vs θ-agrees γ-agrees refl
  L-smaller : length changes-L < _
  L-smaller = subst (length changes-L <_) measure-eq
    (left-before-right-step-shorter changes-L changes-M changes-A change)
complete-interpret-primitive solver measure-eq world-agreement W⊢
    runtime runtime-env environment L-image M-image L⊢ M⊢
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace vV
    | primitive-trace-decomposition
        changes-L changes-M (change ∷ changes-A) f u vf vu
        L-trace M-trace (↠-step root active-tail) refl
    | nL , W₁ , F , L-eq
    with align-interpret-return {n = nL} {changes = changes-L}
      world-agreement (interpreter-term-no-bullet L-image) L-agrees
      L-trace vf L-eq
  where
  L-agrees = term-trace-agreement τ vs θ-agrees γ-agrees refl
complete-interpret-primitive solver measure-eq world-agreement W⊢
    runtime runtime-env environment L-image M-image L⊢ M⊢
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace vV
    | primitive-trace-decomposition
        changes-L changes-M (change ∷ changes-A) f u vf vu
        L-trace M-trace (↠-step root active-tail) refl
    | nL , W₁ , F , L-eq | path-L , F-agrees
    with interpret-returned-typing nL W⊢ runtime runtime-env
      environment L-image L⊢ L-eq
complete-interpret-primitive solver measure-eq world-agreement W⊢
    runtime runtime-env environment L-image M-image L⊢ M⊢
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace vV
    | primitive-trace-decomposition
        changes-L changes-M (change ∷ changes-A) f u vf vu
        L-trace M-trace (↠-step root active-tail) refl
    | nL , W₁ , F , L-eq | path-L , F-agrees
    | W≤W₁ , W₁⊢ , F⊢
    with solver M-smaller
      (interpret-problem refl agreement-L W₁⊢
        (runtime-context-weaken W≤W₁ runtime) runtime-env
        (environment-weaken W≤W₁ W₁⊢ environment)
        M-image M⊢ M-agrees₁ M-trace vu)
  where
  agreement-L = world-trace-agreement-++ world-agreement path-L
  M-agrees = term-trace-agreement τ vs θ-agrees γ-agrees refl
  M-agrees₁ = term-trace-path-empty world-agreement path-L M-agrees
  M-smaller : length changes-M < _
  M-smaller = subst (length changes-M <_) measure-eq
    (middle-before-step-shorter changes-L changes-M changes-A change)
complete-interpret-primitive solver measure-eq world-agreement W⊢
    runtime runtime-env environment L-image M-image L⊢ M⊢
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace vV
    | primitive-trace-decomposition
        changes-L changes-M (change ∷ changes-A) f u vf vu
        L-trace M-trace (↠-step root active-tail) refl
    | nL , W₁ , F , L-eq | path-L , F-agrees
    | W≤W₁ , W₁⊢ , F⊢ | nM , W₂ , U , M-eq
    with align-interpret-return {n = nM} {changes = changes-M}
      agreement-L (interpreter-term-no-bullet M-image) M-agrees₁
      M-trace vu M-eq
  where
  agreement-L = world-trace-agreement-++ world-agreement path-L
  M-agrees = term-trace-agreement τ vs θ-agrees γ-agrees refl
  M-agrees₁ = term-trace-path-empty world-agreement path-L M-agrees
complete-interpret-primitive solver measure-eq world-agreement W⊢
    runtime runtime-env environment L-image M-image L⊢ M⊢
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace vV
    | primitive-trace-decomposition
        changes-L changes-M (change ∷ changes-A) f u vf vu
        L-trace M-trace (↠-step root active-tail) refl
    | nL , W₁ , F , L-eq | path-L , F-agrees
    | W≤W₁ , W₁⊢ , F⊢ | nM , W₂ , U , M-eq
    | path-M , U-agrees
    with interpret-returned-typing nM W₁⊢
      (runtime-context-weaken W≤W₁ runtime) runtime-env
      (environment-weaken W≤W₁ W₁⊢ environment)
      M-image M⊢ M-eq
complete-interpret-primitive {W = W} {γ = γ} {θ = θ}
    {L = L} {M = M}
    solver measure-eq world-agreement W⊢
    runtime runtime-env environment L-image M-image L⊢ M⊢
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace vV
    | primitive-trace-decomposition
        changes-L changes-M (change ∷ changes-A) f u vf vu
        L-trace M-trace (↠-step root active-tail) refl
    | nL , W₁ , .(constant _) , L-eq
    | path-L , F-agrees
    | W≤W₁ , W₁⊢ , constant-typed
    | nM , W₂ , .(constant _) , M-eq
    | path-M , U-agrees
    | W₁≤W₂ , W₂⊢ , constant-typed =
  suc (nL + nM) , W₂ , _ ,
    interpret-primitive-from-phases
      {W = W} {γ = γ} {θ = θ} {L = L} {M = M}
      {nL = nL} {W₁ = W₁} {nM = nM} {W₂ = W₂}
      L-eq M-eq refl

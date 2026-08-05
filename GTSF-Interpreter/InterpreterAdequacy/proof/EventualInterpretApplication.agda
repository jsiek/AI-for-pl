module InterpreterAdequacy.proof.EventualInterpretApplication where

-- File Charter:
--   * Constructs a finite interpreter return for a terminating source
--     application by splitting its call-by-value trace into three phases.
--   * Aligns the worlds and values returned by the two operand calls before
--     invoking the active value-application layer.
--   * Receives recursive completeness only through `StrictlySmallerSolver`.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_; _++_; length)
open import Data.Nat using (_+_; _<_; suc)
open import Data.Product using (_,_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (subst)

open import Interpreter
open import InterpreterAdequacy.TraceAgreement
open import InterpreterAdequacy.proof.ApplicationTraceDecomposition
open import InterpreterAdequacy.proof.EventualApplyLayer using
  (complete-apply-after-root)
open import InterpreterAdequacy.proof.EventualReturnAlignment using
  (align-interpret-return)
open import InterpreterAdequacy.proof.EventualReturnProblem
open import InterpreterAdequacy.proof.EventualReturnTyping using
  (interpret-returned-typing)
open import InterpreterAdequacy.proof.FiniteRunComposition using
  (interpret-application-from-phases)
open import InterpreterAdequacy.proof.TraceAgreementPath using
  (term-trace-path-empty; value-trace-path-empty)
open import InterpreterAdequacy.proof.TraceAgreementProperties using
  (world-trace-agreement-++)
open import InterpreterAdequacy.proof.TraceMeasure using
  ( left-before-right-step-shorter
  ; middle-before-step-shorter
  ; residual-after-two-prefixes-shorter
  )
import Types
open import Typing.InterpreterSemanticTypingCore
open import SmallStepInterface.InterpreterTermShape using (InterpreterTerm)
open import NuReduction
import NuTerms as N
open import proof.InterpreterSemanticTypingProperties using
  ( environment-weaken
  ; runtime-context-weaken
  ; value-weaken
  ; world-extension-trans
  )
open import InterpreterAdequacy.proof.InterpreterTermNoBullet using
  (interpreter-term-no-bullet)

complete-interpret-application :
  ∀ {measure W prefix Δ Σ Γ γ θ L M P A B changes v} →
  StrictlySmallerSolver measure →
  length changes ≡ measure →
  (world-agreement : WorldTraceAgreement W prefix) →
  (W⊢ : WorldTyping W) →
  (runtime : RuntimeContext W Δ Σ θ) →
  (runtime-env : RuntimeTypeEnvironment θ) →
  (environment : EnvironmentTyping W θ γ Γ) →
  (L-image : InterpreterTerm L) →
  (M-image : InterpreterTerm M) →
  N._∣_∣_⊢_⦂_ Δ Σ Γ L (A Types.⇒ B) →
  N._∣_∣_⊢_⦂_ Δ Σ Γ M A →
  TermTraceAgreement world-agreement [] γ θ (L N.· M) P →
  P —↠[ changes ] v →
  N.Value v →
  Σ[ n ∈ StepIndex ]
  Σ[ Z ∈ World ]
  Σ[ R ∈ Value ] interpret W γ θ (L N.· M) n ≡ returned Z R
complete-interpret-application {measure = measure}
    solver measure-eq world-agreement W⊢
    runtime runtime-env environment L-image M-image L⊢ M⊢
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace vV
    with decompose-application-value-trace trace′ vV
  where
  trace′ = subst
    (\ Q → Q —↠[ _ ] _)
    reification trace
complete-interpret-application {measure = measure}
    solver measure-eq world-agreement W⊢
    runtime runtime-env environment L-image M-image L⊢ M⊢
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace vV
    | application-trace-decomposition
        changes-L changes-M .(change ∷ tail-changes) f u vf vu
        L-trace M-trace
          (↠-step {χ = change} {χs = tail-changes} root active-tail) refl
    with solver L-smaller
      (interpret-problem refl world-agreement W⊢ runtime runtime-env
        environment L-image L⊢ L-agrees L-trace vf)
  where
  L-agrees = term-trace-agreement τ vs θ-agrees γ-agrees refl
  L-smaller : length changes-L < _
  L-smaller = subst (length changes-L <_)
    measure-eq
    (left-before-right-step-shorter
      changes-L changes-M tail-changes change)
complete-interpret-application {measure = measure}
    solver measure-eq world-agreement W⊢
    runtime runtime-env environment L-image M-image L⊢ M⊢
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace vV
    | application-trace-decomposition
        changes-L changes-M .(change ∷ tail-changes) f u vf vu
        L-trace M-trace
          (↠-step {χ = change} {χs = tail-changes} root active-tail) refl
    | nL , W₁ , F , L-eq
    with align-interpret-return {n = nL} {changes = changes-L}
      world-agreement (interpreter-term-no-bullet L-image) L-agrees
      L-trace vf L-eq
  where
  L-agrees = term-trace-agreement τ vs θ-agrees γ-agrees refl
complete-interpret-application {measure = measure}
    solver measure-eq world-agreement W⊢
    runtime runtime-env environment L-image M-image L⊢ M⊢
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace vV
    | application-trace-decomposition
        changes-L changes-M .(change ∷ tail-changes) f u vf vu
        L-trace M-trace
          (↠-step {χ = change} {χs = tail-changes} root active-tail) refl
    | nL , W₁ , F , L-eq | path-L , F-agrees
    with interpret-returned-typing nL W⊢ runtime runtime-env
      environment L-image L⊢ L-eq
complete-interpret-application {measure = measure}
    solver measure-eq world-agreement W⊢
    runtime runtime-env environment L-image M-image L⊢ M⊢
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace vV
    | application-trace-decomposition
        changes-L changes-M .(change ∷ tail-changes) f u vf vu
        L-trace M-trace
          (↠-step {χ = change} {χs = tail-changes} root active-tail) refl
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
  M-agrees₁ = term-trace-path-empty
    world-agreement path-L M-agrees
  M-smaller : length changes-M < _
  M-smaller = subst (length changes-M <_)
    measure-eq
    (middle-before-step-shorter
      changes-L changes-M tail-changes change)
complete-interpret-application {measure = measure}
    solver measure-eq world-agreement W⊢
    runtime runtime-env environment L-image M-image L⊢ M⊢
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace vV
    | application-trace-decomposition
        changes-L changes-M .(change ∷ tail-changes) f u vf vu
        L-trace M-trace
          (↠-step {χ = change} {χs = tail-changes} root active-tail) refl
    | nL , W₁ , F , L-eq | path-L , F-agrees
    | W≤W₁ , W₁⊢ , F⊢ | nM , W₂ , U , M-eq
    with align-interpret-return {n = nM} {changes = changes-M}
      agreement-L (interpreter-term-no-bullet M-image) M-agrees₁
      M-trace vu M-eq
  where
  agreement-L = world-trace-agreement-++ world-agreement path-L
  M-agrees = term-trace-agreement τ vs θ-agrees γ-agrees refl
  M-agrees₁ = term-trace-path-empty
    world-agreement path-L M-agrees
complete-interpret-application {measure = measure}
    solver measure-eq world-agreement W⊢
    runtime runtime-env environment L-image M-image L⊢ M⊢
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace vV
    | application-trace-decomposition
        changes-L changes-M .(change ∷ tail-changes) f u vf vu
        L-trace M-trace
          (↠-step {χ = change} {χs = tail-changes} root active-tail) refl
    | nL , W₁ , F , L-eq | path-L , F-agrees
    | W≤W₁ , W₁⊢ , F⊢ | nM , W₂ , U , M-eq
    | path-M , U-agrees
    with interpret-returned-typing nM W₁⊢
      (runtime-context-weaken W≤W₁ runtime) runtime-env
      (environment-weaken W≤W₁ W₁⊢ environment)
      M-image M⊢ M-eq
complete-interpret-application {measure = measure}
    solver measure-eq world-agreement W⊢
    runtime runtime-env environment L-image M-image L⊢ M⊢
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace vV
    | application-trace-decomposition
        changes-L changes-M .(change ∷ tail-changes) f u vf vu
        L-trace M-trace
          (↠-step {χ = change} {χs = tail-changes} root active-tail) refl
    | nL , W₁ , F , L-eq | path-L , F-agrees
    | W≤W₁ , W₁⊢ , F⊢ | nM , W₂ , U , M-eq
    | path-M , U-agrees | W₁≤W₂ , W₂⊢ , U⊢
    with complete-apply-after-root {measure = measure} {W = W₂}
      {F = F} {U = U} {f = applyTerms changes-M f} {u = u}
      {changes = change ∷ tail-changes}
      solver agreement-LM W₂⊢ F⊢₂ U⊢
      F-agrees₂ U-agrees root active-tail vV tail-smaller
  where
  agreement-L = world-trace-agreement-++ world-agreement path-L
  agreement-LM = world-trace-agreement-++ agreement-L path-M
  F⊢₂ = value-weaken W₁≤W₂ W₂⊢ F⊢
  F-agrees₂ = value-trace-path-empty agreement-L path-M F-agrees
  tail-smaller : length tail-changes < _
  tail-smaller = subst (length tail-changes <_)
    measure-eq
    (residual-after-two-prefixes-shorter
      changes-L changes-M tail-changes change)
complete-interpret-application {W = W} {γ = γ} {θ = θ}
    {L = L} {M = M}
    solver measure-eq world-agreement W⊢
    runtime runtime-env environment L-image M-image L⊢ M⊢
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace vV
    | application-trace-decomposition
        changes-L changes-M .(change ∷ tail-changes) f u vf vu
        L-trace M-trace
          (↠-step {χ = change} {χs = tail-changes} root active-tail) refl
    | nL , W₁ , F , L-eq | path-L , F-agrees
    | W≤W₁ , W₁⊢ , F⊢ | nM , W₂ , U , M-eq
    | path-M , U-agrees | W₁≤W₂ , W₂⊢ , U⊢
    | nA , W₃ , R , A-eq =
  suc (nL + (nM + nA)) , W₃ , R ,
    interpret-application-from-phases
      {W = W} {γ = γ} {θ = θ} {L = L} {M = M}
      {nL = nL} {W₁ = W₁} {F = F}
      {nM = nM} {W₂ = W₂} {U = U}
      {nA = nA} {W₃ = W₃} {R = R} L-eq M-eq A-eq

module InterpreterAdequacy.proof.EventualInterpretPrimitiveBlame where

-- File Charter:
--   * Constructs finite blamed interpreter runs for source addition.
--   * Handles blame in either operand after synchronizing preceding phases.
--   * Excludes active blame from typed numeric operands by an explicit
--     one-step numeric result trace.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Data.List using ([]; length)
open import Data.Nat using (_+_; _<_; suc)
open import Data.Product using (_,_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (subst)

open import Interpreter
open import InterpreterAdequacy.TraceAgreement
open import InterpreterAdequacy.proof.EventualBlameProblem
open import InterpreterAdequacy.proof.EventualReturnAlignment using
  (align-interpret-return)
import InterpreterAdequacy.proof.EventualReturnProblem as Return
open import InterpreterAdequacy.proof.EventualReturnDriver using
  (eventual-return)
open import InterpreterAdequacy.proof.EventualReturnTyping using
  (interpret-returned-typing)
open import InterpreterAdequacy.proof.FiniteRunComposition using
  ( interpret-primitive-from-left-blame
  ; interpret-primitive-from-right-blame
  )
open import InterpreterAdequacy.proof.InterpreterTermNoBullet using
  (interpreter-term-no-bullet)
open import InterpreterAdequacy.proof.PrimitiveBlameTraceDecomposition
open import InterpreterAdequacy.proof.TraceAgreementPath using
  (term-trace-path-empty; value-trace-path-empty)
open import InterpreterAdequacy.proof.TraceAgreementProperties using
  (world-trace-agreement-++)
open import InterpreterAdequacy.proof.TraceMeasure using
  (middle-before-step-shorter; prefix-before-step-shorter)
open import Typing.InterpreterSemanticTypingCore
open import SmallStepInterface.InterpreterTermShape using (InterpreterTerm)
open import NuReduction
import NuTerms as N
open import Primitives using (addℕ)
open import proof.DGG.Core.NuReductionDeterminism using
  (source-blame-excludes-value)
open import proof.InterpreterSemanticTypingProperties using
  (environment-weaken; runtime-context-weaken)
open import Types using (`ℕ; ‵_)

constant-trace-term :
  ∀ {W changes}
    {world-agreement : WorldTraceAgreement W changes}
    {Ξ κ v} →
  ValueTraceAgreement world-agreement Ξ (constant κ) v →
  v ≡ N.$ κ
constant-trace-term constant-trace-agrees = refl

complete-interpret-primitive-blame :
  ∀ {measure W prefix Δ Σ Γ γ θ L M P changes} →
  StrictlySmallerBlameSolver measure →
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
  P —↠[ changes ] N.blame →
  Σ[ n ∈ StepIndex ] Σ[ Z ∈ World ]
    interpret W γ θ (L N.⊕[ addℕ ] M) n ≡ blamed Z
complete-interpret-primitive-blame {measure = measure}
    solver measure-eq world-agreement W⊢
    runtime runtime-env environment L-image M-image L⊢ M⊢
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace
    with decompose-primitive-blame-trace trace′
  where
  trace′ = subst (λ Q → Q —↠[ _ ] N.blame) reification trace

complete-interpret-primitive-blame {measure = measure}
    solver measure-eq world-agreement W⊢
    runtime runtime-env environment L-image M-image L⊢ M⊢
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace | left-blames {changes-L = changes-L} L-trace refl
    with solver L-smaller
      (interpret-problem refl world-agreement W⊢ runtime runtime-env
        environment L-image L⊢ L-agrees L-trace)
  where
  L-agrees = term-trace-agreement τ vs θ-agrees γ-agrees refl
  L-smaller : length changes-L < measure
  L-smaller = subst (length changes-L <_) measure-eq
    (prefix-before-step-shorter changes-L [] keep)
complete-interpret-primitive-blame {W = W} {γ = γ} {θ = θ}
    {L = L} {M = M}
    solver measure-eq world-agreement W⊢
    runtime runtime-env environment L-image M-image L⊢ M⊢
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace | left-blames L-trace refl | nL , Z , L-eq =
  suc nL , Z , interpret-primitive-from-left-blame
    {W = W} {γ = γ} {θ = θ} {L = L} {M = M}
    {n = nL} {Z = Z} L-eq

complete-interpret-primitive-blame {measure = measure}
    solver measure-eq world-agreement W⊢
    runtime runtime-env environment L-image M-image L⊢ M⊢
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace
    | right-blames {changes-L = changes-L} {changes-M = changes-M}
        vf L-trace M-trace refl
    with eventual-return
      (Return.interpret-problem refl world-agreement W⊢
        runtime runtime-env environment L-image L⊢ L-agrees
        L-trace vf)
  where
  L-agrees = term-trace-agreement τ vs θ-agrees γ-agrees refl
complete-interpret-primitive-blame {measure = measure}
    solver measure-eq world-agreement W⊢
    runtime runtime-env environment L-image M-image L⊢ M⊢
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace
    | right-blames {changes-L = changes-L} {changes-M = changes-M}
        vf L-trace M-trace refl | nL , W₁ , F , L-eq
    with align-interpret-return {n = nL} {changes = changes-L}
      world-agreement (interpreter-term-no-bullet L-image) L-agrees
      L-trace vf L-eq
  where
  L-agrees = term-trace-agreement τ vs θ-agrees γ-agrees refl
complete-interpret-primitive-blame {measure = measure}
    solver measure-eq world-agreement W⊢
    runtime runtime-env environment L-image M-image L⊢ M⊢
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace
    | right-blames {changes-L = changes-L} {changes-M = changes-M}
        vf L-trace M-trace refl | nL , W₁ , F , L-eq
    | path-L , F-agrees
    with interpret-returned-typing nL W⊢ runtime runtime-env
      environment L-image L⊢ L-eq
complete-interpret-primitive-blame {measure = measure}
    solver measure-eq world-agreement W⊢
    runtime runtime-env environment L-image M-image L⊢ M⊢
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace
    | right-blames {changes-L = changes-L} {changes-M = changes-M}
        vf L-trace M-trace refl | nL , W₁ , F , L-eq
    | path-L , F-agrees | W≤W₁ , W₁⊢ , F⊢
    with solver M-smaller
      (interpret-problem refl agreement-L W₁⊢
        (runtime-context-weaken W≤W₁ runtime) runtime-env
        (environment-weaken W≤W₁ W₁⊢ environment)
        M-image M⊢ M-agrees₁ M-trace)
  where
  agreement-L = world-trace-agreement-++ world-agreement path-L
  M-agrees = term-trace-agreement τ vs θ-agrees γ-agrees refl
  M-agrees₁ = term-trace-path-empty world-agreement path-L M-agrees
  M-smaller : length changes-M < measure
  M-smaller = subst (length changes-M <_) measure-eq
    (middle-before-step-shorter changes-L changes-M [] keep)
complete-interpret-primitive-blame {W = W} {γ = γ} {θ = θ}
    {L = L} {M = M}
    solver measure-eq world-agreement W⊢
    runtime runtime-env environment L-image M-image L⊢ M⊢
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace
    | right-blames {changes-L = changes-L} {changes-M = changes-M}
        vf L-trace M-trace refl | nL , W₁ , F , L-eq
    | path-L , F-agrees | W≤W₁ , W₁⊢ , F⊢
    | nM , Z , M-eq =
  suc (nL + nM) , Z , interpret-primitive-from-right-blame
    {W = W} {γ = γ} {θ = θ} {L = L} {M = M}
    {nL = nL} {W₁ = W₁} {V = F} {nM = nM} {Z = Z}
    L-eq M-eq

-- Typed numeric values make the active blame branch impossible.
complete-interpret-primitive-blame {measure = measure}
    solver measure-eq world-agreement W⊢
    runtime runtime-env environment L-image M-image L⊢ M⊢
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace
    | active-blames {changes-L = changes-L} {changes-M = changes-M}
        vf vu L-trace M-trace active-trace refl
    with eventual-return
      (Return.interpret-problem refl world-agreement W⊢
        runtime runtime-env environment L-image L⊢ L-agrees
        L-trace vf)
  where
  L-agrees = term-trace-agreement τ vs θ-agrees γ-agrees refl
complete-interpret-primitive-blame {measure = measure}
    solver measure-eq world-agreement W⊢
    runtime runtime-env environment L-image M-image L⊢ M⊢
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace
    | active-blames {changes-L = changes-L} {changes-M = changes-M}
        vf vu L-trace M-trace active-trace refl
    | nL , W₁ , F , L-eq
    with align-interpret-return {n = nL} {changes = changes-L}
      world-agreement (interpreter-term-no-bullet L-image) L-agrees
      L-trace vf L-eq
  where
  L-agrees = term-trace-agreement τ vs θ-agrees γ-agrees refl
complete-interpret-primitive-blame {measure = measure}
    solver measure-eq world-agreement W⊢
    runtime runtime-env environment L-image M-image L⊢ M⊢
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace
    | active-blames {changes-L = changes-L} {changes-M = changes-M}
        vf vu L-trace M-trace active-trace refl
    | nL , W₁ , F , L-eq | path-L , F-agrees
    with interpret-returned-typing nL W⊢ runtime runtime-env
      environment L-image L⊢ L-eq
complete-interpret-primitive-blame {measure = measure}
    solver measure-eq world-agreement W⊢
    runtime runtime-env environment L-image M-image L⊢ M⊢
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace
    | active-blames {changes-L = changes-L} {changes-M = changes-M}
        vf vu L-trace M-trace active-trace refl
    | nL , W₁ , .(constant _) , L-eq
    | path-L , F-agrees
    | W≤W₁ , W₁⊢ , constant-typed {n = m}
    with eventual-return
      (Return.interpret-problem refl agreement-L W₁⊢
        (runtime-context-weaken W≤W₁ runtime) runtime-env
        (environment-weaken W≤W₁ W₁⊢ environment)
        M-image M⊢ M-agrees₁ M-trace vu)
  where
  agreement-L = world-trace-agreement-++ world-agreement path-L
  M-agrees = term-trace-agreement τ vs θ-agrees γ-agrees refl
  M-agrees₁ = term-trace-path-empty world-agreement path-L M-agrees
complete-interpret-primitive-blame {measure = measure}
    solver measure-eq world-agreement W⊢
    runtime runtime-env environment L-image M-image L⊢ M⊢
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace
    | active-blames {changes-L = changes-L} {changes-M = changes-M}
        vf vu L-trace M-trace active-trace refl
    | nL , W₁ , .(constant _) , L-eq
    | path-L , F-agrees
    | W≤W₁ , W₁⊢ , constant-typed {n = m}
    | nM , W₂ , U , M-eq
    with align-interpret-return {n = nM} {changes = changes-M}
      agreement-L (interpreter-term-no-bullet M-image) M-agrees₁
      M-trace vu M-eq
  where
  agreement-L = world-trace-agreement-++ world-agreement path-L
  M-agrees = term-trace-agreement τ vs θ-agrees γ-agrees refl
  M-agrees₁ = term-trace-path-empty world-agreement path-L M-agrees
complete-interpret-primitive-blame {measure = measure}
    solver measure-eq world-agreement W⊢
    runtime runtime-env environment L-image M-image L⊢ M⊢
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace
    | active-blames {changes-L = changes-L} {changes-M = changes-M}
        vf vu L-trace M-trace active-trace refl
    | nL , W₁ , .(constant _) , L-eq
    | path-L , F-agrees
    | W≤W₁ , W₁⊢ , constant-typed {n = m}
    | nM , W₂ , U , M-eq | path-M , U-agrees
    with interpret-returned-typing nM W₁⊢
      (runtime-context-weaken W≤W₁ runtime) runtime-env
      (environment-weaken W≤W₁ W₁⊢ environment)
      M-image M⊢ M-eq
complete-interpret-primitive-blame {measure = measure}
    solver measure-eq world-agreement W⊢
    runtime runtime-env environment L-image M-image L⊢ M⊢
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace
    | active-blames {changes-L = changes-L} {changes-M = changes-M}
        vf vu L-trace M-trace active-trace refl
    | nL , W₁ , .(constant _) , L-eq
    | path-L , F-agrees | W≤W₁ , W₁⊢ , constant-typed
    | nM , W₂ , .(constant _) , M-eq
    | path-M , U-agrees
    | W₁≤W₂ , W₂⊢ , constant-typed {n = n}
    with constant-trace-term
      (value-trace-path-empty agreement-L path-M F-agrees)
       | constant-trace-term U-agrees
  where
  agreement-L = world-trace-agreement-++ world-agreement path-L
complete-interpret-primitive-blame {measure = measure}
    solver measure-eq world-agreement W⊢
    runtime runtime-env environment L-image M-image L⊢ M⊢
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace
    | active-blames {changes-L = changes-L} {changes-M = changes-M}
        vf vu L-trace M-trace active-trace refl
    | nL , W₁ , .(constant _) , L-eq
    | path-L , F-agrees
    | W≤W₁ , W₁⊢ , constant-typed {n = m}
    | nM , W₂ , .(constant _) , M-eq
    | path-M , U-agrees
    | W₁≤W₂ , W₂⊢ , constant-typed {n = n}
    | F-term-eq | U-term-eq =
  ⊥-elim
    (source-blame-excludes-value active-trace′
      (↠-step (pure-step δ-⊕) ↠-refl) (N.$ _))
  where
  active-trace₁ = subst
    (λ f′ → (f′ N.⊕[ addℕ ] _) —↠[ _ ] N.blame)
    F-term-eq active-trace
  active-trace′ = subst
    (λ u′ → (N.$ (Primitives.κℕ m) N.⊕[ addℕ ] u′)
      —↠[ _ ] N.blame)
    U-term-eq active-trace₁

module InterpreterAdequacy.proof.EventualInterpretApplicationBlame where

-- File Charter:
--   * Constructs a finite blamed interpreter run for source applications.
--   * Separates blame in the left operand, right operand, and active
--     application, synchronizing each preceding successful phase.
--   * Consumes the active application root before recursive blame solving.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_; length)
open import Data.Nat using (_+_; _<_; suc)
open import Data.Product using (_,_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (subst)

open import Interpreter
open import InterpreterAdequacy.TraceAgreement
open import InterpreterAdequacy.proof.ApplicationBlameTraceDecomposition
open import InterpreterAdequacy.proof.EventualApplyBlameLayer using
  (complete-apply-blame-after-root)
open import InterpreterAdequacy.proof.EventualBlameProblem
open import InterpreterAdequacy.proof.EventualReturnAlignment using
  (align-interpret-return)
import InterpreterAdequacy.proof.EventualReturnProblem as Return
open import InterpreterAdequacy.proof.EventualReturnDriver using
  (eventual-return)
open import InterpreterAdequacy.proof.EventualReturnTyping using
  (interpret-returned-typing)
open import InterpreterAdequacy.proof.FiniteRunComposition using
  ( interpret-application-from-active-blame
  ; interpret-application-from-left-blame
  ; interpret-application-from-right-blame
  )
open import InterpreterAdequacy.proof.InterpreterTermNoBullet using
  (interpreter-term-no-bullet)
open import InterpreterAdequacy.proof.TraceAgreementPath using
  (term-trace-path-empty; value-trace-path-empty)
open import InterpreterAdequacy.proof.TraceAgreementProperties using
  (world-trace-agreement-++)
open import InterpreterAdequacy.proof.TraceMeasure using
  ( middle-before-step-shorter
  ; prefix-before-step-shorter
  ; residual-after-two-prefixes-shorter
  )
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
import Types

complete-interpret-application-blame :
  ∀ {measure W prefix Δ Σ Γ γ θ L M P A B changes} →
  StrictlySmallerBlameSolver measure →
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
  P —↠[ changes ] N.blame →
  Σ[ n ∈ StepIndex ] Σ[ Z ∈ World ]
    interpret W γ θ (L N.· M) n ≡ blamed Z
complete-interpret-application-blame {measure = measure}
    solver measure-eq world-agreement W⊢
    runtime runtime-env environment L-image M-image L⊢ M⊢
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace
    with decompose-application-blame-trace trace′
  where
  trace′ = subst (λ Q → Q —↠[ _ ] N.blame) reification trace

complete-interpret-application-blame {measure = measure}
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
complete-interpret-application-blame {W = W} {γ = γ} {θ = θ}
    {L = L} {M = M}
    solver measure-eq world-agreement W⊢
    runtime runtime-env environment L-image M-image L⊢ M⊢
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace | left-blames L-trace refl | nL , Z , L-eq =
  suc nL , Z , interpret-application-from-left-blame
    {W = W} {γ = γ} {θ = θ} {L = L} {M = M}
    {n = nL} {Z = Z} L-eq

complete-interpret-application-blame {measure = measure}
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
complete-interpret-application-blame {measure = measure}
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
complete-interpret-application-blame {measure = measure}
    solver measure-eq world-agreement W⊢
    runtime runtime-env environment L-image M-image L⊢ M⊢
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace
    | right-blames {changes-L = changes-L} {changes-M = changes-M}
        vf L-trace M-trace refl | nL , W₁ , F , L-eq
    | path-L , F-agrees
    with interpret-returned-typing nL W⊢ runtime runtime-env
      environment L-image L⊢ L-eq
complete-interpret-application-blame {measure = measure}
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
complete-interpret-application-blame {W = W} {γ = γ} {θ = θ}
    {L = L} {M = M}
    solver measure-eq world-agreement W⊢
    runtime runtime-env environment L-image M-image L⊢ M⊢
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace
    | right-blames {changes-L = changes-L} {changes-M = changes-M}
        vf L-trace M-trace refl | nL , W₁ , F , L-eq
    | path-L , F-agrees | W≤W₁ , W₁⊢ , F⊢
    | nM , Z , M-eq =
  suc (nL + nM) , Z , interpret-application-from-right-blame
    {W = W} {γ = γ} {θ = θ} {L = L} {M = M}
    {nL = nL} {W₁ = W₁} {F = F} {nM = nM} {Z = Z}
    L-eq M-eq

complete-interpret-application-blame {measure = measure}
    solver measure-eq world-agreement W⊢
    runtime runtime-env environment L-image M-image L⊢ M⊢
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace
    | active-blames {changes-L = changes-L} {changes-M = changes-M}
        {changes-A = change ∷ changes-A}
        vf vu L-trace M-trace (↠-step root active-tail) refl
    with eventual-return
      (Return.interpret-problem refl world-agreement W⊢
        runtime runtime-env environment L-image L⊢ L-agrees
        L-trace vf)
  where
  L-agrees = term-trace-agreement τ vs θ-agrees γ-agrees refl
complete-interpret-application-blame {measure = measure}
    solver measure-eq world-agreement W⊢
    runtime runtime-env environment L-image M-image L⊢ M⊢
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace
    | active-blames {changes-L = changes-L} {changes-M = changes-M}
        {changes-A = change ∷ changes-A}
        vf vu L-trace M-trace (↠-step root active-tail) refl
    | nL , W₁ , F , L-eq
    with align-interpret-return {n = nL} {changes = changes-L}
      world-agreement (interpreter-term-no-bullet L-image) L-agrees
      L-trace vf L-eq
  where
  L-agrees = term-trace-agreement τ vs θ-agrees γ-agrees refl
complete-interpret-application-blame {measure = measure}
    solver measure-eq world-agreement W⊢
    runtime runtime-env environment L-image M-image L⊢ M⊢
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace
    | active-blames {changes-L = changes-L} {changes-M = changes-M}
        {changes-A = change ∷ changes-A}
        vf vu L-trace M-trace (↠-step root active-tail) refl
    | nL , W₁ , F , L-eq | path-L , F-agrees
    with interpret-returned-typing nL W⊢ runtime runtime-env
      environment L-image L⊢ L-eq
complete-interpret-application-blame {measure = measure}
    solver measure-eq world-agreement W⊢
    runtime runtime-env environment L-image M-image L⊢ M⊢
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace
    | active-blames {changes-L = changes-L} {changes-M = changes-M}
        {changes-A = change ∷ changes-A}
        vf vu L-trace M-trace (↠-step root active-tail) refl
    | nL , W₁ , F , L-eq | path-L , F-agrees
    | W≤W₁ , W₁⊢ , F⊢
    with eventual-return
      (Return.interpret-problem refl agreement-L W₁⊢
        (runtime-context-weaken W≤W₁ runtime) runtime-env
        (environment-weaken W≤W₁ W₁⊢ environment)
        M-image M⊢ M-agrees₁ M-trace vu)
  where
  agreement-L = world-trace-agreement-++ world-agreement path-L
  M-agrees = term-trace-agreement τ vs θ-agrees γ-agrees refl
  M-agrees₁ = term-trace-path-empty world-agreement path-L M-agrees
complete-interpret-application-blame {measure = measure}
    solver measure-eq world-agreement W⊢
    runtime runtime-env environment L-image M-image L⊢ M⊢
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace
    | active-blames {changes-L = changes-L} {changes-M = changes-M}
        {changes-A = change ∷ changes-A}
        vf vu L-trace M-trace (↠-step root active-tail) refl
    | nL , W₁ , F , L-eq | path-L , F-agrees
    | W≤W₁ , W₁⊢ , F⊢ | nM , W₂ , U , M-eq
    with align-interpret-return {n = nM} {changes = changes-M}
      agreement-L (interpreter-term-no-bullet M-image) M-agrees₁
      M-trace vu M-eq
  where
  agreement-L = world-trace-agreement-++ world-agreement path-L
  M-agrees = term-trace-agreement τ vs θ-agrees γ-agrees refl
  M-agrees₁ = term-trace-path-empty world-agreement path-L M-agrees
complete-interpret-application-blame {measure = measure}
    solver measure-eq world-agreement W⊢
    runtime runtime-env environment L-image M-image L⊢ M⊢
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace
    | active-blames {changes-L = changes-L} {changes-M = changes-M}
        {changes-A = change ∷ changes-A}
        vf vu L-trace M-trace (↠-step root active-tail) refl
    | nL , W₁ , F , L-eq | path-L , F-agrees
    | W≤W₁ , W₁⊢ , F⊢ | nM , W₂ , U , M-eq
    | path-M , U-agrees
    with interpret-returned-typing nM W₁⊢
      (runtime-context-weaken W≤W₁ runtime) runtime-env
      (environment-weaken W≤W₁ W₁⊢ environment)
      M-image M⊢ M-eq
complete-interpret-application-blame {measure = measure}
    solver measure-eq world-agreement W⊢
    runtime runtime-env environment L-image M-image L⊢ M⊢
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace
    | active-blames {changes-L = changes-L} {changes-M = changes-M}
        {changes-A = change ∷ changes-A}
        vf vu L-trace M-trace (↠-step root active-tail) refl
    | nL , W₁ , F , L-eq | path-L , F-agrees
    | W≤W₁ , W₁⊢ , F⊢ | nM , W₂ , U , M-eq
    | path-M , U-agrees | W₁≤W₂ , W₂⊢ , U⊢
    with complete-apply-blame-after-root {measure = measure} {W = W₂}
      {F = F} {U = U} {f = applyTerms changes-M _} {u = _}
      solver agreement-LM W₂⊢ F⊢₂ U⊢ F-agrees₂ U-agrees
      root active-tail tail-smaller
  where
  agreement-L = world-trace-agreement-++ world-agreement path-L
  agreement-LM = world-trace-agreement-++ agreement-L path-M
  F⊢₂ = value-weaken W₁≤W₂ W₂⊢ F⊢
  F-agrees₂ = value-trace-path-empty agreement-L path-M F-agrees
  tail-smaller : length changes-A < measure
  tail-smaller = subst (length changes-A <_) measure-eq
    (residual-after-two-prefixes-shorter
      changes-L changes-M changes-A change)
complete-interpret-application-blame {W = W} {γ = γ} {θ = θ}
    {L = L} {M = M}
    solver measure-eq world-agreement W⊢
    runtime runtime-env environment L-image M-image L⊢ M⊢
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace
    | active-blames {changes-L = changes-L} {changes-M = changes-M}
        {changes-A = change ∷ changes-A}
        vf vu L-trace M-trace (↠-step root active-tail) refl
    | nL , W₁ , F , L-eq | path-L , F-agrees
    | W≤W₁ , W₁⊢ , F⊢ | nM , W₂ , U , M-eq
    | path-M , U-agrees | W₁≤W₂ , W₂⊢ , U⊢
    | nA , Z , A-eq =
  suc (nL + (nM + nA)) , Z ,
    interpret-application-from-active-blame
      {W = W} {γ = γ} {θ = θ} {L = L} {M = M}
      {nL = nL} {W₁ = W₁} {F = F}
      {nM = nM} {W₂ = W₂} {U = U}
      {nA = nA} {Z = Z} L-eq M-eq A-eq

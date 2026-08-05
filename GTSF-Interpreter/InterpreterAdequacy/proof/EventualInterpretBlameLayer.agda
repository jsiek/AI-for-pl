module InterpreterAdequacy.proof.EventualInterpretBlameLayer where

-- File Charter:
--   * Constructs finite blamed `interpret` runs from source traces to blame.
--   * Delegates compound source forms to small blame-completeness modules.
--   * Synchronizes a successful cast operand, then consumes the active
--     coercion root before recursive blame solving.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Data.List using ([]; _∷_; length)
open import Data.Nat using (_+_; _<_; suc)
open import Data.Product using (_,_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import Interpreter
open import InterpreterAdequacy.TraceAgreement
open import InterpreterAdequacy.proof.CastBlameTraceDecomposition
open import InterpreterAdequacy.proof.EventualBlameProblem
open import InterpreterAdequacy.proof.EventualCoerceBlameLayer using
  (complete-coerce-blame-after-root)
open import InterpreterAdequacy.proof.EventualInterpretApplicationBlame using
  (complete-interpret-application-blame)
open import InterpreterAdequacy.proof.EventualInterpretNuBlame using
  (complete-interpret-nu-blame)
open import InterpreterAdequacy.proof.EventualInterpretPrimitiveBlame using
  (complete-interpret-primitive-blame)
open import InterpreterAdequacy.proof.EventualReturnAlignment using
  (align-interpret-return)
import InterpreterAdequacy.proof.EventualReturnProblem as Return
open import InterpreterAdequacy.proof.EventualReturnDriver using
  (eventual-return)
open import InterpreterAdequacy.proof.EventualReturnTyping using
  (interpret-returned-typing)
open import InterpreterAdequacy.proof.FiniteRunComposition using
  (interpret-cast-from-active-blame; interpret-cast-from-operand-blame)
open import InterpreterAdequacy.proof.InterpreterTermNoBullet using
  (interpreter-term-no-bullet)
open import InterpreterAdequacy.proof.SyntaxReification using
  (lookup-environment-trace)
open import InterpreterAdequacy.proof.TraceAgreementPath using
  (type-environment-trace-rebase)
open import InterpreterAdequacy.proof.TraceAgreementProperties using
  (value-trace-value; world-trace-agreement-++)
open import InterpreterAdequacy.proof.TraceMeasure using
  (prefix-before-step-shorter; residual-after-step-shorter)
open import InterpreterAdequacy.proof.TypeEnvironmentTracePath
open import Typing.InterpreterSemanticTypingCore
open import SmallStepInterface.InterpreterTermShape
open import NuReduction
import NuTerms as N
open import Primitives using (addℕ)
open import proof.Core.Properties.NuTermProperties using
  (renameᵗᵐ-preserves-Value; substˣᵐ-preserves-Value)
open import proof.DGG.Core.NuReductionDeterminism using
  (source-blame-excludes-value)
open import proof.InterpreterSemanticTypingProperties using
  (environment-lookup-sound; runtime-context-weaken)
open import Types using (extᵗ)

complete-interpret-blame :
  ∀ {measure W prefix Δ Σ Γ γ θ M P A changes} →
  StrictlySmallerBlameSolver measure →
  length changes ≡ measure →
  (world-agreement : WorldTraceAgreement W prefix) →
  (W⊢ : WorldTyping W) →
  (runtime : RuntimeContext W Δ Σ θ) →
  (runtime-env : RuntimeTypeEnvironment θ) →
  (environment : EnvironmentTyping W θ γ Γ) →
  (image : InterpreterTerm M) →
  N._∣_∣_⊢_⦂_ Δ Σ Γ M A →
  TermTraceAgreement world-agreement [] γ θ M P →
  P —↠[ changes ] N.blame →
  Σ[ n ∈ StepIndex ] Σ[ Z ∈ World ]
    interpret W γ θ M n ≡ blamed Z

complete-interpret-blame solver measure-eq world-agreement W⊢ runtime
    runtime-env environment (variable-term x) (N.⊢` x∈)
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace
    with environment-lookup-sound environment x∈
complete-interpret-blame solver measure-eq world-agreement W⊢ runtime
    runtime-env environment (variable-term x) (N.⊢` x∈)
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace | V , lookup-eq , V⊢
    with lookup-environment-trace γ-agrees lookup-eq
complete-interpret-blame solver measure-eq world-agreement W⊢ runtime
    runtime-env environment (variable-term x) (N.⊢` x∈)
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace | V , lookup-eq , V⊢ | u , environment-eq , V-agrees =
  ⊥-elim
    (source-blame-excludes-value trace ↠-refl source-value)
  where
  source-value = subst N.Value
    (sym (trans reification environment-eq))
    (value-trace-value V-agrees)

complete-interpret-blame solver measure-eq world-agreement W⊢ runtime
    runtime-env environment (closure-term M-image) M⊢
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace rewrite reification =
  ⊥-elim
    (source-blame-excludes-value trace ↠-refl (N.ƛ _))

complete-interpret-blame solver measure-eq world-agreement W⊢ runtime
    runtime-env environment
    (application-term L-image M-image) (N.⊢· L⊢ M⊢)
    agreement trace =
  complete-interpret-application-blame solver measure-eq
    world-agreement W⊢ runtime runtime-env environment
    L-image M-image L⊢ M⊢ agreement trace

complete-interpret-blame solver measure-eq world-agreement W⊢ runtime
    runtime-env environment (type-abstraction-term vU U-image) M⊢
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace rewrite reification =
  ⊥-elim
    (source-blame-excludes-value trace ↠-refl source-value)
  where
  source-value = N.Λ
    (substˣᵐ-preserves-Value _
      (renameᵗᵐ-preserves-Value (extᵗ τ) vU))

complete-interpret-blame solver measure-eq world-agreement W⊢ runtime
    runtime-env environment (instantiation-term L-image) M⊢
    agreement trace =
  complete-interpret-nu-blame solver measure-eq world-agreement W⊢
    runtime runtime-env environment L-image M⊢ agreement trace

complete-interpret-blame solver measure-eq world-agreement W⊢ runtime
    runtime-env environment (constant-term κ) M⊢
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace rewrite reification =
  ⊥-elim
    (source-blame-excludes-value trace ↠-refl (N.$ κ))

complete-interpret-blame solver measure-eq world-agreement W⊢ runtime
    runtime-env environment
    (primitive-term addℕ L-image M-image) (N.⊢⊕ L⊢ .addℕ M⊢)
    agreement trace =
  complete-interpret-primitive-blame solver measure-eq world-agreement
    W⊢ runtime runtime-env environment L-image M-image L⊢ M⊢
    agreement trace

complete-interpret-blame {measure = measure}
    {W = W} {γ = γ} {θ = θ} {M = M N.⟨ c ⟩}
    solver measure-eq world-agreement W⊢ runtime runtime-env environment
    (coercion-application-term M-image) (N.⊢⟨⟩ c⊢ M⊢)
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace
    with decompose-cast-blame-trace trace′
  where
  trace′ = subst (λ Q → Q —↠[ _ ] N.blame) reification trace

complete-interpret-blame {measure = measure}
    {W = W} {γ = γ} {θ = θ} {M = M N.⟨ c ⟩}
    solver measure-eq world-agreement W⊢ runtime runtime-env environment
    (coercion-application-term M-image) (N.⊢⟨⟩ c⊢ M⊢)
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace
    | operand-blames {changes-M = changes-M} M-trace refl
    with solver M-smaller
      (interpret-problem refl world-agreement W⊢ runtime runtime-env
        environment M-image M⊢ M-agrees M-trace)
  where
  M-agrees = term-trace-agreement τ vs θ-agrees γ-agrees refl
  M-smaller : length changes-M < measure
  M-smaller = subst (length changes-M <_) measure-eq
    (prefix-before-step-shorter changes-M [] keep)
complete-interpret-blame {W = W} {γ = γ} {θ = θ}
    {M = M N.⟨ c ⟩}
    solver measure-eq world-agreement W⊢ runtime runtime-env environment
    (coercion-application-term M-image) (N.⊢⟨⟩ c⊢ M⊢)
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace | operand-blames M-trace refl | nM , Z , M-eq =
  suc nM , Z , interpret-cast-from-operand-blame
    {W = W} {γ = γ} {θ = θ} {M = M} {c = c}
    {n = nM} {Z = Z} M-eq

complete-interpret-blame {measure = measure}
    {W = W} {γ = γ} {θ = θ} {M = M N.⟨ c ⟩}
    solver measure-eq world-agreement W⊢ runtime runtime-env environment
    (coercion-application-term M-image) (N.⊢⟨⟩ c⊢ M⊢)
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace
    | active-blames {changes-M = changes-M}
        {changes-C = change ∷ changes-C}
        vu M-trace (↠-step root C-tail) refl
    with eventual-return
      (Return.interpret-problem refl world-agreement W⊢ runtime
        runtime-env environment M-image M⊢ M-agrees M-trace vu)
  where
  M-agrees = term-trace-agreement τ vs θ-agrees γ-agrees refl
complete-interpret-blame {measure = measure}
    {W = W} {γ = γ} {θ = θ} {M = M N.⟨ c ⟩}
    solver measure-eq world-agreement W⊢ runtime runtime-env environment
    (coercion-application-term M-image) (N.⊢⟨⟩ c⊢ M⊢)
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace
    | active-blames {changes-M = changes-M}
        {changes-C = change ∷ changes-C}
        vu M-trace (↠-step root C-tail) refl
    | nM , W₁ , U , M-eq
    with align-interpret-return {n = nM} {changes = changes-M}
      world-agreement (interpreter-term-no-bullet M-image) M-agrees
      M-trace vu M-eq
  where
  M-agrees = term-trace-agreement τ vs θ-agrees γ-agrees refl
complete-interpret-blame {measure = measure}
    {W = W} {γ = γ} {θ = θ} {M = M N.⟨ c ⟩}
    solver measure-eq world-agreement W⊢ runtime runtime-env environment
    (coercion-application-term M-image) (N.⊢⟨⟩ c⊢ M⊢)
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace
    | active-blames {changes-M = changes-M}
        {changes-C = change ∷ changes-C}
        vu M-trace (↠-step root C-tail) refl
    | nM , W₁ , U , M-eq | path-M , U-agrees
    with interpret-returned-typing nM W⊢ runtime runtime-env
      environment M-image M⊢ M-eq
complete-interpret-blame {measure = measure}
    {W = W} {γ = γ} {θ = θ} {M = M N.⟨ c ⟩}
    solver measure-eq world-agreement W⊢ runtime runtime-env environment
    (coercion-application-term M-image) (N.⊢⟨⟩ c⊢ M⊢)
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace
    | active-blames {changes-M = changes-M}
        {changes-C = change ∷ changes-C}
        vu M-trace (↠-step root C-tail) refl
    | nM , W₁ , U , M-eq | path-M , U-agrees
    | W≤W₁ , W₁⊢ , U⊢
    with type-environment-trace-path world-agreement path-M θ-agrees
complete-interpret-blame {measure = measure}
    {W = W} {γ = γ} {θ = θ} {M = M N.⟨ c ⟩}
    solver measure-eq world-agreement W⊢ runtime runtime-env environment
    (coercion-application-term M-image) (N.⊢⟨⟩ c⊢ M⊢)
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace
    | active-blames {changes-M = changes-M}
        {changes-C = change ∷ changes-C}
        vu M-trace (↠-step root C-tail) refl
    | nM , W₁ , U , M-eq | path-M , U-agrees
    | W≤W₁ , W₁⊢ , U⊢ | path-agreement
    with complete-coerce-blame-after-root {measure = measure}
      {W = W₁} solver agreement-M W₁⊢
      (runtime-context-weaken W≤W₁ runtime) runtime-env c⊢ U⊢
      (type-environment-trace-rebase
        (final-agreement path-agreement)) U-agrees C-root C-tail
      tail-smaller
  where
  agreement-M = world-trace-agreement-++ world-agreement path-M
  final-eq = coercion-action path-agreement c
  C-root = subst
    (λ d → _ N.⟨ d ⟩ —→[ change ] _)
    (sym final-eq) root
  tail-smaller : length changes-C < measure
  tail-smaller = subst (length changes-C <_) measure-eq
    (residual-after-step-shorter changes-M changes-C change)
complete-interpret-blame {W = W} {γ = γ} {θ = θ}
    {M = M N.⟨ c ⟩}
    solver measure-eq world-agreement W⊢ runtime runtime-env environment
    (coercion-application-term M-image) (N.⊢⟨⟩ c⊢ M⊢)
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace
    | active-blames {changes-M = changes-M}
        {changes-C = change ∷ changes-C}
        vu M-trace (↠-step root C-tail) refl
    | nM , W₁ , U , M-eq | path-M , U-agrees
    | W≤W₁ , W₁⊢ , U⊢ | path-agreement
    | nC , Z , C-eq =
  suc (nM + nC) , Z , interpret-cast-from-active-blame
    {W = W} {γ = γ} {θ = θ} {M = M} {c = c}
    {nM = nM} {W₁ = W₁} {V = U} {nC = nC} {Z = Z}
    M-eq C-eq

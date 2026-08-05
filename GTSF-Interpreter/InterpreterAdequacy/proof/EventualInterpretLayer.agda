module InterpreterAdequacy.proof.EventualInterpretLayer where

-- File Charter:
--   * Constructs a finite `interpret` return from a terminating trace of a
--     reified interpreter term.
--   * Recurses structurally on interpreter source terms for inert casts and
--     delegates genuinely shorter dynamic phases to `StrictlySmallerSolver`.
--   * Uses proved return alignment, but no normalization or non-convergence
--     premise.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Data.List using ([]; _∷_; length)
open import Data.List.Properties using (++-identityʳ)
open import Data.Maybe using (just)
open import Data.Nat using (_+_; _<_; suc; zero)
open import Data.Product using (_,_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)

import Coercions as C
open import Interpreter
open import InterpreterAdequacy.TraceAgreement
open import InterpreterAdequacy.proof.CastTraceDecomposition
open import InterpreterAdequacy.proof.EventualCoerceLayer using
  (complete-coerce-after-root; complete-coerce-refl)
open import InterpreterAdequacy.proof.EventualInterpretApplication using
  (complete-interpret-application)
open import InterpreterAdequacy.proof.EventualInterpretNu using
  (complete-interpret-nu)
open import InterpreterAdequacy.proof.EventualInterpretPrimitive using
  (complete-interpret-primitive)
open import InterpreterAdequacy.proof.EventualReturnAlignment using
  (align-interpret-return)
open import InterpreterAdequacy.proof.EventualReturnProblem
open import InterpreterAdequacy.proof.EventualReturnTyping using
  (interpret-returned-typing)
open import InterpreterAdequacy.proof.FiniteRunComposition using
  (interpret-cast-from-phases)
open import InterpreterAdequacy.proof.InterpreterTermNoBullet using
  (interpreter-term-no-bullet)
open import InterpreterAdequacy.proof.InterpreterValueCompleteness using
  (interpret-value-completeᵢ)
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
  (value-irreducible)
open import proof.InterpreterSemanticTypingProperties using
  (environment-lookup-sound; runtime-context-weaken)
open import Types using (extᵗ)

complete-interpret :
  ∀ {measure W prefix Δ Σ Γ γ θ M P A changes v} →
  StrictlySmallerSolver measure →
  length changes ≡ measure →
  (world-agreement : WorldTraceAgreement W prefix) →
  (W⊢ : WorldTyping W) →
  (runtime : RuntimeContext W Δ Σ θ) →
  (runtime-env : RuntimeTypeEnvironment θ) →
  (environment : EnvironmentTyping W θ γ Γ) →
  (image : InterpreterTerm M) →
  N._∣_∣_⊢_⦂_ Δ Σ Γ M A →
  TermTraceAgreement world-agreement [] γ θ M P →
  P —↠[ changes ] v →
  N.Value v →
  Σ[ n ∈ StepIndex ]
  Σ[ Z ∈ World ]
  Σ[ R ∈ Value ] interpret W γ θ M n ≡ returned Z R

complete-interpret solver measure-eq world-agreement W⊢ runtime
    runtime-env environment image M⊢ agreement ↠-refl vP
    with interpret-value-completeᵢ world-agreement runtime runtime-env
      environment image M⊢ agreement vP
complete-interpret solver measure-eq world-agreement W⊢ runtime
    runtime-env environment image M⊢ agreement ↠-refl vP
    | n , V , result-eq , V-agrees =
  n , _ , V , result-eq

complete-interpret solver measure-eq world-agreement W⊢ runtime
    runtime-env environment (variable-term x) (N.⊢` x∈)
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    (↠-step root tail) vV
    with environment-lookup-sound environment x∈
complete-interpret solver measure-eq world-agreement W⊢ runtime
    runtime-env environment (variable-term x) (N.⊢` x∈)
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    (↠-step root tail) vV
    | V , lookup-eq , V⊢
    with lookup-environment-trace γ-agrees lookup-eq
complete-interpret solver measure-eq world-agreement W⊢ runtime
    runtime-env environment (variable-term x) (N.⊢` x∈)
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    (↠-step root tail) vV
    | V , lookup-eq , V⊢ | u , environment-eq , V-agrees =
  ⊥-elim (value-irreducible source-value root)
  where
  source-value = subst N.Value (sym (trans reification environment-eq))
    (value-trace-value V-agrees)

complete-interpret solver measure-eq world-agreement W⊢ runtime
    runtime-env environment (closure-term M-image) M⊢
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    (↠-step root tail) vV
    rewrite reification =
  ⊥-elim (value-irreducible (N.ƛ _) root)

complete-interpret solver measure-eq world-agreement W⊢ runtime
    runtime-env environment
    (application-term L-image M-image) (N.⊢· L⊢ M⊢)
    agreement trace vV =
  complete-interpret-application solver measure-eq world-agreement W⊢
    runtime runtime-env environment L-image M-image L⊢ M⊢
    agreement trace vV

complete-interpret solver measure-eq world-agreement W⊢ runtime
    runtime-env environment
    (type-abstraction-term vU U-image) M⊢
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    (↠-step root tail) vV
    rewrite reification =
  ⊥-elim (value-irreducible source-value root)
  where
  source-value = N.Λ
    (substˣᵐ-preserves-Value _
      (renameᵗᵐ-preserves-Value (extᵗ τ) vU))

complete-interpret solver measure-eq world-agreement W⊢ runtime
    runtime-env environment (instantiation-term L-image) M⊢
    agreement trace vV =
  complete-interpret-nu solver measure-eq world-agreement W⊢ runtime
    runtime-env environment L-image M⊢ agreement trace vV

complete-interpret solver measure-eq world-agreement W⊢ runtime
    runtime-env environment (constant-term κ) M⊢
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    (↠-step root tail) vV
    rewrite reification =
  ⊥-elim (value-irreducible (N.$ κ) root)

complete-interpret solver measure-eq world-agreement W⊢ runtime
    runtime-env environment
    (primitive-term addℕ L-image M-image) (N.⊢⊕ L⊢ .addℕ M⊢)
    agreement trace vV =
  complete-interpret-primitive solver measure-eq world-agreement W⊢
    runtime runtime-env environment L-image M-image L⊢ M⊢
    agreement trace vV

complete-interpret {W = W} {γ = γ} {θ = θ} {M = M N.⟨ c ⟩}
    solver measure-eq world-agreement W⊢ runtime
    runtime-env environment (coercion-application-term M-image)
    (N.⊢⟨⟩ c⊢ M⊢)
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace vV
    with decompose-cast-value-trace trace′ vV
  where
  trace′ = subst (\ Q → Q —↠[ _ ] _) reification trace

complete-interpret {W = W} {γ = γ} {θ = θ} {M = M N.⟨ c ⟩}
    solver measure-eq world-agreement W⊢ runtime
    runtime-env environment (coercion-application-term M-image)
    (N.⊢⟨⟩ c⊢ M⊢)
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace vV
    | cast-trace-decomposition changes-M [] u vu M-trace ↠-refl refl
    with complete-interpret solver M-measure-eq world-agreement W⊢ runtime
      runtime-env environment M-image M⊢ M-agrees M-trace vu
  where
  M-agrees = term-trace-agreement τ vs θ-agrees γ-agrees refl
  M-measure-eq = trans (cong length (sym (++-identityʳ changes-M)))
    measure-eq

complete-interpret {W = W} {γ = γ} {θ = θ} {M = M N.⟨ c ⟩}
    solver measure-eq world-agreement W⊢ runtime
    runtime-env environment (coercion-application-term M-image)
    (N.⊢⟨⟩ c⊢ M⊢)
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace vV
    | cast-trace-decomposition changes-M [] u vu M-trace ↠-refl refl
    | nM , W₁ , U , M-eq
    with align-interpret-return {n = nM} {changes = changes-M}
      world-agreement (interpreter-term-no-bullet M-image) M-agrees
      M-trace vu M-eq
  where
  M-agrees = term-trace-agreement τ vs θ-agrees γ-agrees refl

complete-interpret {W = W} {γ = γ} {θ = θ} {M = M N.⟨ c ⟩}
    solver measure-eq world-agreement W⊢ runtime
    runtime-env environment (coercion-application-term M-image)
    (N.⊢⟨⟩ c⊢ M⊢)
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace vV
    | cast-trace-decomposition changes-M [] u vu M-trace ↠-refl refl
    | nM , W₁ , U , M-eq | path-M , U-agrees
    with interpret-returned-typing nM W⊢ runtime runtime-env
      environment M-image M⊢ M-eq

complete-interpret {W = W} {γ = γ} {θ = θ} {M = M N.⟨ c ⟩}
    solver measure-eq world-agreement W⊢ runtime
    runtime-env environment (coercion-application-term M-image)
    (N.⊢⟨⟩ c⊢ M⊢)
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace vV
    | cast-trace-decomposition changes-M [] u vu M-trace ↠-refl refl
    | nM , W₁ , U , M-eq | path-M , U-agrees
    | W≤W₁ , W₁⊢ , U⊢
    with type-environment-trace-path world-agreement path-M θ-agrees

complete-interpret {W = W} {γ = γ} {θ = θ} {M = M N.⟨ c ⟩}
    solver measure-eq world-agreement W⊢ runtime
    runtime-env environment (coercion-application-term M-image)
    (N.⊢⟨⟩ c⊢ M⊢)
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace vV
    | cast-trace-decomposition changes-M [] u vu M-trace ↠-refl refl
    | nM , W₁ , U , M-eq | path-M , U-agrees
    | W≤W₁ , W₁⊢ , U⊢ | path-agreement
    with complete-coerce-refl agreement-M W₁⊢
      (runtime-context-weaken W≤W₁ runtime) runtime-env c⊢ U⊢
      (type-environment-trace-rebase (final-agreement path-agreement))
      U-agrees cast-value
  where
  agreement-M = world-trace-agreement-++ world-agreement path-M
  cast-value = subst (\ d → N.Value (u N.⟨ d ⟩))
    (sym (coercion-action path-agreement c)) vV

complete-interpret {W = W} {γ = γ} {θ = θ} {M = M N.⟨ c ⟩}
    solver measure-eq world-agreement W⊢ runtime
    runtime-env environment (coercion-application-term M-image)
    (N.⊢⟨⟩ c⊢ M⊢)
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace vV
    | cast-trace-decomposition changes-M [] u vu M-trace ↠-refl refl
    | nM , W₁ , U , M-eq | path-M , U-agrees
    | W≤W₁ , W₁⊢ , U⊢ | path-agreement
    | nC , W₂ , R , C-eq =
  suc (nM + nC) , W₂ , R ,
    interpret-cast-from-phases
      {W = W} {γ = γ} {θ = θ} {M = M} {c = c}
      {nM = nM} {W₁ = W₁} {V = U} {nC = nC} {W₂ = W₂} {R = R}
      M-eq C-eq

complete-interpret {W = W} {γ = γ} {θ = θ} {M = M N.⟨ c ⟩}
    solver measure-eq world-agreement W⊢ runtime
    runtime-env environment (coercion-application-term M-image)
    (N.⊢⟨⟩ c⊢ M⊢)
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace vV
    | cast-trace-decomposition changes-M (change ∷ changes-C)
        u vu M-trace active refl
    with solver M-smaller
      (interpret-problem refl world-agreement W⊢ runtime runtime-env
        environment M-image M⊢ M-agrees M-trace vu)
  where
  M-agrees = term-trace-agreement τ vs θ-agrees γ-agrees refl
  M-smaller : length changes-M < _
  M-smaller = subst (length changes-M <_) measure-eq
    (prefix-before-step-shorter changes-M changes-C change)

complete-interpret {W = W} {γ = γ} {θ = θ} {M = M N.⟨ c ⟩}
    solver measure-eq world-agreement W⊢ runtime
    runtime-env environment (coercion-application-term M-image)
    (N.⊢⟨⟩ c⊢ M⊢)
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace vV
    | cast-trace-decomposition changes-M (change ∷ changes-C)
        u vu M-trace active refl
    | nM , W₁ , U , M-eq
    with align-interpret-return {n = nM} {changes = changes-M}
      world-agreement (interpreter-term-no-bullet M-image) M-agrees
      M-trace vu M-eq
  where
  M-agrees = term-trace-agreement τ vs θ-agrees γ-agrees refl

complete-interpret {W = W} {γ = γ} {θ = θ} {M = M N.⟨ c ⟩}
    solver measure-eq world-agreement W⊢ runtime
    runtime-env environment (coercion-application-term M-image)
    (N.⊢⟨⟩ c⊢ M⊢)
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace vV
    | cast-trace-decomposition changes-M (change ∷ changes-C)
        u vu M-trace active refl
    | nM , W₁ , U , M-eq | path-M , U-agrees
    with interpret-returned-typing nM W⊢ runtime runtime-env
      environment M-image M⊢ M-eq

complete-interpret {W = W} {γ = γ} {θ = θ} {M = M N.⟨ c ⟩}
    solver measure-eq world-agreement W⊢ runtime
    runtime-env environment (coercion-application-term M-image)
    (N.⊢⟨⟩ c⊢ M⊢)
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace vV
    | cast-trace-decomposition changes-M (change ∷ changes-C)
        u vu M-trace active refl
    | nM , W₁ , U , M-eq | path-M , U-agrees
    | W≤W₁ , W₁⊢ , U⊢
    with type-environment-trace-path world-agreement path-M θ-agrees

complete-interpret {W = W} {γ = γ} {θ = θ} {M = M N.⟨ c ⟩}
    solver measure-eq world-agreement W⊢ runtime
    runtime-env environment (coercion-application-term M-image)
    (N.⊢⟨⟩ c⊢ M⊢)
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace vV
    | cast-trace-decomposition changes-M (change ∷ changes-C)
        u vu M-trace active refl
    | nM , W₁ , U , M-eq | path-M , U-agrees
    | W≤W₁ , W₁⊢ , U⊢ | path-agreement
    with active′
  where
  active′ = subst
    (\ d → (u N.⟨ d ⟩) —↠[ change ∷ changes-C ] _)
    (sym (coercion-action path-agreement c)) active

complete-interpret {W = W} {γ = γ} {θ = θ} {M = M N.⟨ c ⟩}
    solver measure-eq world-agreement W⊢ runtime
    runtime-env environment (coercion-application-term M-image)
    (N.⊢⟨⟩ c⊢ M⊢)
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace vV
    | cast-trace-decomposition changes-M (change ∷ changes-C)
        u vu M-trace active refl
    | nM , W₁ , U , M-eq | path-M , U-agrees
    | W≤W₁ , W₁⊢ , U⊢ | path-agreement
    | ↠-step root active-tail
    with complete-coerce-after-root solver agreement-M W₁⊢
      (runtime-context-weaken W≤W₁ runtime) runtime-env c⊢ U⊢
      (type-environment-trace-rebase (final-agreement path-agreement))
      U-agrees root active-tail vV C-smaller
  where
  agreement-M = world-trace-agreement-++ world-agreement path-M
  C-smaller : length changes-C < _
  C-smaller = subst (length changes-C <_) measure-eq
    (residual-after-step-shorter changes-M changes-C change)

complete-interpret {W = W} {γ = γ} {θ = θ} {M = M N.⟨ c ⟩}
    solver measure-eq world-agreement W⊢ runtime
    runtime-env environment (coercion-application-term M-image)
    (N.⊢⟨⟩ c⊢ M⊢)
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace vV
    | cast-trace-decomposition changes-M (change ∷ changes-C)
        u vu M-trace active refl
    | nM , W₁ , U , M-eq | path-M , U-agrees
    | W≤W₁ , W₁⊢ , U⊢ | path-agreement
    | ↠-step root active-tail | nC , W₂ , R , C-eq =
  suc (nM + nC) , W₂ , R ,
    interpret-cast-from-phases
      {W = W} {γ = γ} {θ = θ} {M = M} {c = c}
      {nM = nM} {W₁ = W₁} {V = U} {nC = nC} {W₂ = W₂} {R = R}
      M-eq C-eq

module InterpreterAdequacy.proof.EventualApplyLayer where

-- File Charter:
--   * Constructs a finite `applyValue` return after consuming the active
--     application root of a terminating value trace.
--   * Handles closures directly and decomposes function proxies into their
--     three strictly smaller phases.
--   * Receives recursive completeness only through `StrictlySmallerSolver`.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Data.List using ([]; _∷_; _++_; length)
open import Data.Nat using (ℕ; _+_; _<_; _≤_; suc)
open import Data.Nat.Properties using (≤-<-trans; ≤-trans)
open import Data.Product using (_,_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym)

import Coercions as C
open import Interpreter
open import InterpreterAdequacy.TraceAgreement
open import InterpreterAdequacy.proof.BetaReification using
  (beta-reification)
open import InterpreterAdequacy.proof.EventualReturnAlignment using
  (align-apply-return; align-coerce-return)
open import InterpreterAdequacy.proof.EventualReturnProblem
open import InterpreterAdequacy.proof.EventualReturnTyping using
  (apply-returned-typing; coerce-returned-typing)
open import InterpreterAdequacy.proof.FiniteRunComposition using
  (apply-closure-from-body; apply-proxy-from-phases)
open import InterpreterAdequacy.proof.ProxyTraceDecomposition
open import InterpreterAdequacy.proof.TraceAgreementPath using
  (type-environment-trace-rebase; value-trace-path-empty)
open import InterpreterAdequacy.proof.TraceAgreementProperties using
  (value-trace-value; world-trace-agreement-++; world-trace-path-++)
open import InterpreterAdequacy.proof.TraceMeasure using
  (middle-length≤; prefix-length≤; suffix-length≤)
open import InterpreterAdequacy.proof.TypeEnvironmentTracePath
open import Typing.InterpreterSemanticTypingCore
open import NuReduction
import NuTerms as N
open import proof.InterpreterSemanticTypingProperties using
  (runtime-context-weaken; value-weaken; world-extension-trans)
open import proof.DGG.Core.NuReductionDeterminism using
  (step-deterministic)

complete-apply-after-root :
  ∀ {measure : ℕ} {W : World} {prefix : StoreChanges}
    {F U : Value} {f u v : N.Term} {A B : SemanticType}
    {changes : StoreChanges} →
  StrictlySmallerSolver measure →
  (world-agreement : WorldTraceAgreement W prefix) →
  (W⊢ : WorldTyping W) →
  (F⊢ : ValueTyping W F (A ⇒ᵛ B)) →
  (U⊢ : ValueTyping W U A) →
  (F-agrees : ValueTraceAgreement world-agreement [] F f) →
  (U-agrees : ValueTraceAgreement world-agreement [] U u) →
  ∀ {change : StoreChange} {tail : StoreChanges} {next : N.Term} →
  (f N.· u) —→[ change ] next →
  next —↠[ tail ] v →
  N.Value v →
  length tail < measure →
  Σ[ n ∈ StepIndex ]
  Σ[ Z ∈ World ]
  Σ[ R ∈ Value ] (applyValue W F U n ≡ returned Z R)

complete-apply-after-root {W = W} {U = U} {u = u}
    solver world-agreement W⊢
    (closure-typed {θ = θ} {γ = γ} {N = body}
      W₀⊢ runtime runtime-env environment
      image body⊢)
    U⊢
    (closure-trace-agrees {M = body} {M′ = body′} {τ = τ} {vs = vs}
      θ-agrees γ-agrees no-body reification no-reified-body)
    U-agrees root tail vV tail-smaller
    with step-deterministic
      (pure-step (β (value-trace-value U-agrees))) root
complete-apply-after-root {W = W} {U = U} {u = u}
    solver world-agreement W⊢
    (closure-typed {θ = θ} {γ = γ} {N = body}
      W₀⊢ runtime runtime-env environment
      image body⊢)
    U⊢
    (closure-trace-agrees {M = body} {M′ = body′} {τ = τ} {vs = vs}
      θ-agrees γ-agrees no-body reification no-reified-body)
    U-agrees root tail vV tail-smaller | refl , refl
    with solver tail-smaller
      (interpret-problem refl world-agreement W⊢ runtime runtime-env
        (environment-cons U⊢ environment) image body⊢
        (term-trace-agreement τ (u ∷ vs)
          θ-agrees
          (environment-cons-trace-agrees U-agrees γ-agrees)
          (beta-reification {M = body} {M′ = body′}
            τ vs u reification))
        tail vV)
complete-apply-after-root {W = W} {U = U} {u = u}
    solver world-agreement W⊢
    (closure-typed {θ = θ} {γ = γ} {N = body}
      W₀⊢ runtime runtime-env environment
      image body⊢)
    U⊢
    (closure-trace-agrees {M = body} {M′ = body′} {τ = τ} {vs = vs}
      θ-agrees γ-agrees no-body reification no-reified-body)
    U-agrees root tail vV tail-smaller | refl , refl
    | n , Z , R , body-eq =
  suc n , Z , R , apply-closure-from-body
    {W = W} {N = body} {γ = γ} {θ = θ} {U = U}
    {n = n} {Z = Z} {R = R} body-eq

complete-apply-after-root {W = W} {U = U} {u = u}
    solver world-agreement W⊢
    (function-proxy-typed {θ = θ} {V = base} {p = p} {q = q}
      W₀⊢ runtime runtime-env environment
      (C.cast-fun p⊢ q⊢) base⊢)
    U⊢
    (function-proxy-trace-agrees {τ = τ} {v = base-term}
      θ-agrees base-agrees)
    U-agrees
    root tail vV tail-smaller
    with step-deterministic
      (pure-step (β-↦ (value-trace-value base-agrees)
        (value-trace-value U-agrees))) root
complete-apply-after-root {W = W} {U = U} {u = u}
    solver world-agreement W⊢
    (function-proxy-typed {θ = θ} {V = base} {p = p} {q = q}
      W₀⊢ runtime runtime-env environment
      (C.cast-fun p⊢ q⊢) base⊢)
    U⊢
    (function-proxy-trace-agrees {τ = τ} {v = base-term}
      θ-agrees base-agrees)
    U-agrees
    root tail vV tail-smaller | refl , refl
    with decompose-proxy-tail (value-trace-value base-agrees) tail vV
complete-apply-after-root {W = W} {U = U} {u = u}
    solver world-agreement W⊢
    (function-proxy-typed {θ = θ} {V = base} {p = p} {q = q}
      W₀⊢ runtime runtime-env environment
      (C.cast-fun p⊢ q⊢) base⊢)
    U⊢
    (function-proxy-trace-agrees {τ = τ} {v = base-term}
      θ-agrees base-agrees)
    U-agrees
    root tail vV tail-smaller | refl , refl
    | proxy-trace-decomposition
        changes-P changes-A changes-Q u′ z vu′ vz
        P-trace A-trace Q-trace refl
    with solver P-smaller
      (coerce-problem refl world-agreement W⊢ runtime runtime-env p⊢ U⊢
        θ-agrees U-agrees P-trace vu′)
  where
  P-smaller : length changes-P < _
  P-smaller = ≤-<-trans
    (prefix-length≤ changes-P (changes-A ++ changes-Q))
    tail-smaller
complete-apply-after-root {W = W} {U = U} {u = u}
    solver world-agreement W⊢
    (function-proxy-typed {θ = θ} {V = base} {p = p} {q = q}
      W₀⊢ runtime runtime-env environment
      (C.cast-fun p⊢ q⊢) base⊢)
    U⊢
    (function-proxy-trace-agrees {τ = τ} {v = base-term}
      θ-agrees base-agrees)
    U-agrees
    root tail vV tail-smaller | refl , refl
    | proxy-trace-decomposition
        changes-P changes-A changes-Q u′ z vu′ vz
        P-trace A-trace Q-trace refl
    | nP , W₁ , U′ , P-eq
    with align-coerce-return
      {W = W} {θ = θ} {τ = τ} {c = p} {V = U} {v = u}
      {n = nP} {Z = W₁} {R = U′} {changes = changes-P} {u = u′}
      world-agreement θ-agrees U-agrees P-trace vu′ P-eq
complete-apply-after-root {W = W} {U = U} {u = u}
    solver world-agreement W⊢
    (function-proxy-typed {θ = θ} {V = base} {p = p} {q = q}
      W₀⊢ runtime runtime-env environment
      (C.cast-fun p⊢ q⊢) base⊢)
    U⊢
    (function-proxy-trace-agrees {τ = τ} {v = base-term}
      θ-agrees base-agrees)
    U-agrees
    root tail vV tail-smaller | refl , refl
    | proxy-trace-decomposition
        changes-P changes-A changes-Q u′ z vu′ vz
        P-trace A-trace Q-trace refl
    | nP , W₁ , U′ , P-eq | path-P , U′-agrees
    with coerce-returned-typing nP
      {W = W} {θ = θ} {c = p} {V = U} {Z = W₁} {U = U′}
      W⊢ runtime runtime-env p⊢ U⊢ P-eq
complete-apply-after-root {W = W} {U = U} {u = u}
    solver world-agreement W⊢
    (function-proxy-typed {θ = θ} {V = base} {p = p} {q = q}
      W₀⊢ runtime runtime-env environment
      (C.cast-fun p⊢ q⊢) base⊢)
    U⊢
    (function-proxy-trace-agrees {τ = τ} {v = base-term}
      θ-agrees base-agrees)
    U-agrees
    root tail vV tail-smaller | refl , refl
    | proxy-trace-decomposition
        changes-P changes-A changes-Q u′ z vu′ vz
        P-trace A-trace Q-trace refl
    | nP , W₁ , U′ , P-eq | path-P , U′-agrees
    | W≤W₁ , W₁⊢ , U′⊢
    with solver A-smaller
      (apply-problem refl agreement-P W₁⊢
        (value-weaken W≤W₁ W₁⊢ base⊢) U′⊢
        (value-trace-path-empty world-agreement path-P base-agrees)
        U′-agrees A-trace vz)
  where
  agreement-P = world-trace-agreement-++ world-agreement path-P
  A-smaller : length changes-A < _
  A-smaller = ≤-<-trans
    (middle-length≤ changes-P changes-A changes-Q)
    tail-smaller
complete-apply-after-root {W = W} {U = U} {u = u}
    solver world-agreement W⊢
    (function-proxy-typed {θ = θ} {V = base} {p = p} {q = q}
      W₀⊢ runtime runtime-env environment
      (C.cast-fun p⊢ q⊢) base⊢)
    U⊢
    (function-proxy-trace-agrees {τ = τ} {v = base-term}
      θ-agrees base-agrees)
    U-agrees
    root tail vV tail-smaller | refl , refl
    | proxy-trace-decomposition
        changes-P changes-A changes-Q u′ z vu′ vz
        P-trace A-trace Q-trace refl
    | nP , W₁ , U′ , P-eq | path-P , U′-agrees
    | W≤W₁ , W₁⊢ , U′⊢
    | nA , W₂ , V′ , A-eq
    with align-apply-return
      {W = W₁} {F = base} {U = U′} {n = nA}
      {Z = W₂} {R = V′} {changes = changes-A} {v = z}
      agreement-P
      (value-trace-path-empty world-agreement path-P base-agrees)
      U′-agrees A-trace vz A-eq
  where
  agreement-P = world-trace-agreement-++ world-agreement path-P
complete-apply-after-root {W = W} {U = U} {u = u}
    solver world-agreement W⊢
    (function-proxy-typed {θ = θ} {V = base} {p = p} {q = q}
      W₀⊢ runtime runtime-env environment
      (C.cast-fun p⊢ q⊢) base⊢)
    U⊢
    (function-proxy-trace-agrees {τ = τ} {v = base-term}
      θ-agrees base-agrees)
    U-agrees
    root tail vV tail-smaller | refl , refl
    | proxy-trace-decomposition
        changes-P changes-A changes-Q u′ z vu′ vz
        P-trace A-trace Q-trace refl
    | nP , W₁ , U′ , P-eq | path-P , U′-agrees
    | W≤W₁ , W₁⊢ , U′⊢
    | nA , W₂ , V′ , A-eq | path-A , V′-agrees
    with apply-returned-typing nA
      {W = W₁} {F = base} {U = U′} {Z = W₂} {V = V′} W₁⊢
      (value-weaken W≤W₁ W₁⊢ base⊢) U′⊢ A-eq
complete-apply-after-root {W = W} {U = U} {u = u}
    solver world-agreement W⊢
    (function-proxy-typed {θ = θ} {V = base} {p = p} {q = q}
      W₀⊢ runtime runtime-env environment
      (C.cast-fun p⊢ q⊢) base⊢)
    U⊢
    (function-proxy-trace-agrees {τ = τ} {v = base-term}
      θ-agrees base-agrees)
    U-agrees
    root tail vV tail-smaller | refl , refl
    | proxy-trace-decomposition
        changes-P changes-A changes-Q u′ z vu′ vz
        P-trace A-trace Q-trace refl
    | nP , W₁ , U′ , P-eq | path-P , U′-agrees
    | W≤W₁ , W₁⊢ , U′⊢
    | nA , W₂ , V′ , A-eq | path-A , V′-agrees
    | W₁≤W₂ , W₂⊢ , V′⊢
    with type-environment-trace-path world-agreement
      (world-trace-path-++ path-P path-A) θ-agrees
complete-apply-after-root {W = W} {U = U} {u = u}
    solver world-agreement W⊢
    (function-proxy-typed {θ = θ} {V = base} {p = p} {q = q}
      W₀⊢ runtime runtime-env environment
      (C.cast-fun p⊢ q⊢) base⊢)
    U⊢
    (function-proxy-trace-agrees {τ = τ} {v = base-term}
      θ-agrees base-agrees)
    U-agrees
    root tail vV tail-smaller | refl , refl
    | proxy-trace-decomposition
        changes-P changes-A changes-Q u′ z vu′ vz
        P-trace A-trace Q-trace refl
    | nP , W₁ , U′ , P-eq | path-P , U′-agrees
    | W≤W₁ , W₁⊢ , U′⊢
    | nA , W₂ , V′ , A-eq | path-A , V′-agrees
    | W₁≤W₂ , W₂⊢ , V′⊢
    | path-agreement
    with solver Q-smaller
      (coerce-problem refl agreement-PA W₂⊢
        (runtime-context-weaken
          (world-extension-trans W≤W₁ W₁≤W₂) runtime)
        runtime-env q⊢ V′⊢
        (type-environment-trace-rebase
          (final-agreement path-agreement)) V′-agrees
        Q-trace′ vV)
  where
  agreement-P = world-trace-agreement-++ world-agreement path-P
  agreement-PA = world-trace-agreement-++ agreement-P path-A
  Q-smaller : length changes-Q < _
  Q-smaller = ≤-<-trans
    (≤-trans (suffix-length≤ changes-A changes-Q)
      (suffix-length≤ changes-P (changes-A ++ changes-Q)))
    tail-smaller
  Q-trace′ =
    subst
      (\ d → z N.⟨ d ⟩ —↠[ changes-Q ] _)
      (sym (coercion-action path-agreement _)) Q-trace
complete-apply-after-root {W = W} {U = U} {u = u}
    solver world-agreement W⊢
    (function-proxy-typed {θ = θ} {V = base} {p = p} {q = q}
      W₀⊢ runtime runtime-env environment
      (C.cast-fun p⊢ q⊢) base⊢)
    U⊢
    (function-proxy-trace-agrees {τ = τ} {v = base-term}
      θ-agrees base-agrees)
    U-agrees
    root tail vV tail-smaller | refl , refl
    | proxy-trace-decomposition
        changes-P changes-A changes-Q u′ z vu′ vz
        P-trace A-trace Q-trace refl
    | nP , W₁ , U′ , P-eq | path-P , U′-agrees
    | W≤W₁ , W₁⊢ , U′⊢
    | nA , W₂ , V′ , A-eq | path-A , V′-agrees
    | W₁≤W₂ , W₂⊢ , V′⊢
    | path-agreement | nQ , W₃ , R , Q-eq =
  suc (nP + (nA + nQ)) , W₃ , R ,
    apply-proxy-from-phases
      {W = W} {p = p} {q = q} {θ = θ} {V = base} {U = U}
      {nP = nP} {W₁ = W₁} {U′ = U′} {nA = nA} {W₂ = W₂}
      {V′ = V′} {nQ = nQ} {W₃ = W₃} {R = R}
      P-eq A-eq Q-eq

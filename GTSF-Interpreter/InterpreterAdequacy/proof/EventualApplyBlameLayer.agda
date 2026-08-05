module InterpreterAdequacy.proof.EventualApplyBlameLayer where

-- File Charter:
--   * Constructs finite blamed `applyValue` runs after one active root.
--   * Separates function-proxy blame into input, application, and result
--     phases, recursively solving only strict subtraces.
--   * Uses successful-run completeness to synchronize preceding phases.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Data.List using ([]; _∷_; _++_; length)
open import Data.Nat using (_+_; _<_; suc)
open import Data.Nat.Properties using (<-trans; ≤-<-trans; ≤-trans)
open import Data.Product using (_,_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import Coercions as C
open import Interpreter
open import InterpreterAdequacy.TraceAgreement
open import InterpreterAdequacy.proof.ApplicationBlameTraceDecomposition
open import InterpreterAdequacy.proof.ApplicationTraceDecomposition
open import InterpreterAdequacy.proof.BetaReification using
  (beta-reification)
open import InterpreterAdequacy.proof.CastBlameTraceDecomposition
open import InterpreterAdequacy.proof.EventualBlameProblem
open import InterpreterAdequacy.proof.EventualReturnAlignment using
  (align-apply-return; align-coerce-return)
import InterpreterAdequacy.proof.EventualReturnProblem as Return
open import InterpreterAdequacy.proof.EventualReturnDriver using
  (eventual-return)
open import InterpreterAdequacy.proof.EventualReturnTyping using
  (apply-returned-typing; coerce-returned-typing)
open import InterpreterAdequacy.proof.FiniteRunComposition using
  ( apply-closure-from-body-blame
  ; apply-proxy-from-application-blame
  ; apply-proxy-from-first-blame
  ; apply-proxy-from-result-blame
  )
open import InterpreterAdequacy.proof.TraceAgreementPath using
  (type-environment-trace-rebase; value-trace-path-empty)
open import InterpreterAdequacy.proof.TraceAgreementProperties using
  (value-trace-value; world-trace-agreement-++; world-trace-path-++)
open import InterpreterAdequacy.proof.TraceMeasure using
  (middle-length≤; prefix-before-step-shorter; prefix-length≤;
   suffix-length≤)
open import InterpreterAdequacy.proof.TypeEnvironmentTracePath
open import Typing.InterpreterSemanticTypingCore
open import NuReduction
import NuTerms as N
open import proof.DGG.Core.NuReductionDeterminism using
  (source-blame-excludes-value; step-deterministic)
open import proof.InterpreterSemanticTypingProperties using
  (runtime-context-weaken; value-weaken; world-extension-trans)

complete-apply-blame-after-root :
  ∀ {measure W prefix F U f u A B change tail next} →
  StrictlySmallerBlameSolver measure →
  (world-agreement : WorldTraceAgreement W prefix) →
  (W⊢ : WorldTyping W) →
  (F⊢ : ValueTyping W F (A ⇒ᵛ B)) →
  (U⊢ : ValueTyping W U A) →
  (F-agrees : ValueTraceAgreement world-agreement [] F f) →
  (U-agrees : ValueTraceAgreement world-agreement [] U u) →
  (f N.· u) —→[ change ] next →
  next —↠[ tail ] N.blame →
  length tail < measure →
  Σ[ n ∈ StepIndex ] Σ[ Z ∈ World ]
    applyValue W F U n ≡ blamed Z

complete-apply-blame-after-root {W = W} {U = U} {u = u}
    solver world-agreement W⊢
    (closure-typed { θ = θ} {γ = γ} {N = body}
      W₀⊢ runtime runtime-env environment image body⊢)
    U⊢
    (closure-trace-agrees {M = body} {M′ = body′} {τ = τ} {vs = vs}
      θ-agrees γ-agrees no-body reification no-reified-body)
    U-agrees root tail tail-smaller
    with step-deterministic
      (pure-step (β (value-trace-value U-agrees))) root
complete-apply-blame-after-root {W = W} {U = U} {u = u}
    solver world-agreement W⊢
    (closure-typed {θ = θ} {γ = γ} {N = body}
      W₀⊢ runtime runtime-env environment image body⊢)
    U⊢
    (closure-trace-agrees {M = body} {M′ = body′} {τ = τ} {vs = vs}
      θ-agrees γ-agrees no-body reification no-reified-body)
    U-agrees root tail tail-smaller | refl , refl
    with solver tail-smaller
      (interpret-problem refl world-agreement W⊢ runtime runtime-env
        (environment-cons U⊢ environment) image body⊢
        (term-trace-agreement τ (u ∷ vs) θ-agrees
          (environment-cons-trace-agrees U-agrees γ-agrees)
          (beta-reification {M = body} {M′ = body′}
            τ vs u reification)) tail)
complete-apply-blame-after-root {W = W} {U = U} {u = u}
    solver world-agreement W⊢
    (closure-typed {θ = θ} {γ = γ} {N = body}
      W₀⊢ runtime runtime-env environment image body⊢)
    U⊢
    (closure-trace-agrees {M = body} {M′ = body′} {τ = τ} {vs = vs}
      θ-agrees γ-agrees no-body reification no-reified-body)
    U-agrees root tail tail-smaller | refl , refl | n , Z , body-eq =
  suc n , Z , apply-closure-from-body-blame
    {W = W} {N = body} {γ = γ} {θ = θ} {U = U}
    {n = n} {Z = Z} body-eq

complete-apply-blame-after-root {measure = measure}
    {W = W} {U = U} {u = u}
    solver world-agreement W⊢
    (function-proxy-typed {θ = θ} {V = base} {p = p} {q = q}
      W₀⊢ runtime runtime-env environment (C.cast-fun p⊢ q⊢) base⊢)
    U⊢
    (function-proxy-trace-agrees {τ = τ} {v = base-term}
      θ-agrees base-agrees)
    U-agrees root tail tail-smaller
    with step-deterministic
      (pure-step (β-↦ (value-trace-value base-agrees)
        (value-trace-value U-agrees))) root
complete-apply-blame-after-root {measure = measure}
    {W = W} {U = U} {u = u}
    solver world-agreement W⊢
    (function-proxy-typed {θ = θ} {V = base} {p = p} {q = q}
      W₀⊢ runtime runtime-env environment (C.cast-fun p⊢ q⊢) base⊢)
    U⊢
    (function-proxy-trace-agrees {τ = τ} {v = base-term}
      θ-agrees base-agrees)
    U-agrees root tail tail-smaller | refl , refl
    with decompose-cast-blame-trace tail

-- The inner application blames because its argument coercion blames.
complete-apply-blame-after-root {measure = measure}
    {W = W} {U = U} {u = u}
    solver world-agreement W⊢
    (function-proxy-typed {θ = θ} {V = base} {p = p} {q = q}
      W₀⊢ runtime runtime-env environment (C.cast-fun p⊢ q⊢) base⊢)
    U⊢
    (function-proxy-trace-agrees {τ = τ} {v = base-term}
      θ-agrees base-agrees)
    U-agrees root tail tail-smaller | refl , refl
    | operand-blames inner-trace refl
    with decompose-application-blame-trace inner-trace
complete-apply-blame-after-root {measure = measure}
    {W = W} {U = U} {u = u}
    solver world-agreement W⊢
    (function-proxy-typed {θ = θ} {V = base} {p = p} {q = q}
      W₀⊢ runtime runtime-env environment (C.cast-fun p⊢ q⊢) base⊢)
    U⊢
    (function-proxy-trace-agrees {τ = τ} {v = base-term}
      θ-agrees base-agrees)
    U-agrees root tail tail-smaller | refl , refl
    | operand-blames inner-trace refl
    | left-blames base-trace refl =
  ⊥-elim
    (source-blame-excludes-value base-trace ↠-refl
      (value-trace-value base-agrees))
complete-apply-blame-after-root {measure = measure}
    {W = W} {U = U} {u = u}
    solver world-agreement W⊢
    (function-proxy-typed {θ = θ} {V = base} {p = p} {q = q}
      W₀⊢ runtime runtime-env environment (C.cast-fun p⊢ q⊢) base⊢)
    U⊢
    (function-proxy-trace-agrees {τ = τ} {v = base-term}
      θ-agrees base-agrees)
    U-agrees root tail tail-smaller | refl , refl
    | operand-blames inner-trace refl
    | right-blames vf base-trace P-trace refl
    with value-trace-refl (value-trace-value base-agrees) base-trace
complete-apply-blame-after-root {measure = measure}
    {W = W} {U = U} {u = u}
    solver world-agreement W⊢
    (function-proxy-typed {θ = θ} {V = base} {p = p} {q = q}
      W₀⊢ runtime runtime-env environment (C.cast-fun p⊢ q⊢) base⊢)
    U⊢
    (function-proxy-trace-agrees {τ = τ} {v = base-term}
      θ-agrees base-agrees)
    U-agrees root tail tail-smaller | refl , refl
    | operand-blames inner-trace refl
    | right-blames {changes-M = changes-P}
        vf base-trace P-trace refl | refl , refl
    with solver P-smaller
      (coerce-problem refl world-agreement W⊢ runtime runtime-env p⊢
        U⊢ θ-agrees U-agrees P-trace)
  where
  P-smaller : length changes-P < measure
  P-smaller = <-trans
    (≤-<-trans (prefix-length≤ changes-P (keep ∷ []))
      (prefix-before-step-shorter
        (changes-P ++ keep ∷ []) [] keep))
    tail-smaller
complete-apply-blame-after-root {W = W} {U = U} {u = u}
    solver world-agreement W⊢
    (function-proxy-typed {θ = θ} {V = base} {p = p} {q = q}
      W₀⊢ runtime runtime-env environment (C.cast-fun p⊢ q⊢) base⊢)
    U⊢
    (function-proxy-trace-agrees {τ = τ} {v = base-term}
      θ-agrees base-agrees)
    U-agrees root tail tail-smaller | refl , refl
    | operand-blames inner-trace refl
    | right-blames {changes-M = changes-P}
        vf base-trace P-trace refl | refl , refl
    | nP , Z , P-eq =
  suc nP , Z , apply-proxy-from-first-blame
    {W = W} {p = p} {q = q} {θ = θ} {V = base} {U = U}
    {n = nP} {Z = Z} P-eq

-- The input coercion returns, then the underlying application blames.
complete-apply-blame-after-root {measure = measure}
    {W = W} {U = U} {u = u}
    solver world-agreement W⊢
    (function-proxy-typed {θ = θ} {V = base} {p = p} {q = q}
      W₀⊢ runtime runtime-env environment (C.cast-fun p⊢ q⊢) base⊢)
    U⊢
    (function-proxy-trace-agrees {τ = τ} {v = base-term}
      θ-agrees base-agrees)
    U-agrees root tail tail-smaller | refl , refl
    | operand-blames inner-trace refl
    | active-blames {changes-M = changes-P}
        {changes-A = changes-A}
        vf vu base-trace P-trace A-trace refl
    with value-trace-refl (value-trace-value base-agrees) base-trace
complete-apply-blame-after-root {measure = measure}
    {W = W} {U = U} {u = u}
    solver world-agreement W⊢
    (function-proxy-typed {θ = θ} {V = base} {p = p} {q = q}
      W₀⊢ runtime runtime-env environment (C.cast-fun p⊢ q⊢) base⊢)
    U⊢
    (function-proxy-trace-agrees {τ = τ} {v = base-term}
      θ-agrees base-agrees)
    U-agrees root tail tail-smaller | refl , refl
    | operand-blames inner-trace refl
    | active-blames {changes-M = changes-P}
        {changes-A = changes-A}
        vf vu base-trace P-trace A-trace refl
    | refl , refl
    with eventual-return
      (Return.coerce-problem refl world-agreement W⊢ runtime runtime-env
        p⊢ U⊢ θ-agrees U-agrees P-trace vu)
complete-apply-blame-after-root {measure = measure}
    {W = W} {U = U} {u = u}
    solver world-agreement W⊢
    (function-proxy-typed {θ = θ} {V = base} {p = p} {q = q}
      W₀⊢ runtime runtime-env environment (C.cast-fun p⊢ q⊢) base⊢)
    U⊢
    (function-proxy-trace-agrees {τ = τ} {v = base-term}
      θ-agrees base-agrees)
    U-agrees root tail tail-smaller | refl , refl
    | operand-blames inner-trace refl
    | active-blames {changes-M = changes-P}
        {changes-A = changes-A}
        vf vu base-trace P-trace A-trace refl
    | refl , refl | nP , W₁ , U′ , P-eq
    with align-coerce-return {n = nP}
      world-agreement θ-agrees U-agrees P-trace vu P-eq
complete-apply-blame-after-root {measure = measure}
    {W = W} {U = U} {u = u}
    solver world-agreement W⊢
    (function-proxy-typed {θ = θ} {V = base} {p = p} {q = q}
      W₀⊢ runtime runtime-env environment (C.cast-fun p⊢ q⊢) base⊢)
    U⊢
    (function-proxy-trace-agrees {τ = τ} {v = base-term}
      θ-agrees base-agrees)
    U-agrees root tail tail-smaller | refl , refl
    | operand-blames inner-trace refl
    | active-blames {changes-M = changes-P}
        {changes-A = changes-A}
        vf vu base-trace P-trace A-trace refl
    | refl , refl | nP , W₁ , U′ , P-eq | path-P , U′-agrees
    with coerce-returned-typing nP W⊢ runtime runtime-env p⊢ U⊢ P-eq
complete-apply-blame-after-root {measure = measure}
    {W = W} {U = U} {u = u}
    solver world-agreement W⊢
    (function-proxy-typed {θ = θ} {V = base} {p = p} {q = q}
      W₀⊢ runtime runtime-env environment (C.cast-fun p⊢ q⊢) base⊢)
    U⊢
    (function-proxy-trace-agrees {τ = τ} {v = base-term}
      θ-agrees base-agrees)
    U-agrees root tail tail-smaller | refl , refl
    | operand-blames inner-trace refl
    | active-blames {changes-M = changes-P}
        {changes-A = changes-A}
        vf vu base-trace P-trace A-trace refl
    | refl , refl | nP , W₁ , U′ , P-eq | path-P , U′-agrees
    | W≤W₁ , W₁⊢ , U′⊢
    with solver A-smaller
      (apply-problem refl agreement-P W₁⊢
        (value-weaken W≤W₁ W₁⊢ base⊢) U′⊢
        (value-trace-path-empty world-agreement path-P base-agrees)
        U′-agrees A-trace)
  where
  agreement-P = world-trace-agreement-++ world-agreement path-P
  A-smaller : length changes-A < measure
  A-smaller = <-trans
    (≤-<-trans (suffix-length≤ changes-P changes-A)
      (prefix-before-step-shorter
        (changes-P ++ changes-A) [] keep))
    tail-smaller
complete-apply-blame-after-root {W = W} {U = U} {u = u}
    solver world-agreement W⊢
    (function-proxy-typed {θ = θ} {V = base} {p = p} {q = q}
      W₀⊢ runtime runtime-env environment (C.cast-fun p⊢ q⊢) base⊢)
    U⊢
    (function-proxy-trace-agrees {τ = τ} {v = base-term}
      θ-agrees base-agrees)
    U-agrees root tail tail-smaller | refl , refl
    | operand-blames inner-trace refl
    | active-blames {changes-M = changes-P}
        {changes-A = changes-A}
        vf vu base-trace P-trace A-trace refl
    | refl , refl | nP , W₁ , U′ , P-eq | path-P , U′-agrees
    | W≤W₁ , W₁⊢ , U′⊢ | nA , Z , A-eq =
  suc (nP + nA) , Z , apply-proxy-from-application-blame
    {W = W} {p = p} {q = q} {θ = θ} {V = base} {U = U}
    {nP = nP} {W₁ = W₁} {U′ = U′}
    {nA = nA} {Z = Z} P-eq A-eq

-- The input and application return; the result coercion blames.
complete-apply-blame-after-root {measure = measure}
    {W = W} {U = U} {u = u}
    solver world-agreement W⊢
    (function-proxy-typed {θ = θ} {V = base} {p = p} {q = q}
      W₀⊢ runtime runtime-env environment (C.cast-fun p⊢ q⊢) base⊢)
    U⊢
    (function-proxy-trace-agrees {τ = τ} {v = base-term}
      θ-agrees base-agrees)
    U-agrees root tail tail-smaller | refl , refl
    | active-blames vu inner-trace Q-trace refl
    with decompose-application-value-trace inner-trace vu
complete-apply-blame-after-root {measure = measure}
    {W = W} {U = U} {u = u}
    solver world-agreement W⊢
    (function-proxy-typed {θ = θ} {V = base} {p = p} {q = q}
      W₀⊢ runtime runtime-env environment (C.cast-fun p⊢ q⊢) base⊢)
    U⊢
    (function-proxy-trace-agrees {τ = τ} {v = base-term}
      θ-agrees base-agrees)
    U-agrees root tail tail-smaller | refl , refl
    | active-blames {changes-C = changes-Q}
        vz inner-trace Q-trace refl
    | application-trace-decomposition
        changes-L changes-P changes-A f u′ vf vu′
        base-trace P-trace A-trace refl
    with value-trace-refl (value-trace-value base-agrees) base-trace
complete-apply-blame-after-root {measure = measure}
    {W = W} {U = U} {u = u}
    solver world-agreement W⊢
    (function-proxy-typed {θ = θ} {V = base} {p = p} {q = q}
      W₀⊢ runtime runtime-env environment (C.cast-fun p⊢ q⊢) base⊢)
    U⊢
    (function-proxy-trace-agrees {τ = τ} {v = base-term}
      θ-agrees base-agrees)
    U-agrees root tail tail-smaller | refl , refl
    | active-blames {changes-C = changes-Q}
        vz inner-trace Q-trace refl
    | application-trace-decomposition
        .[] changes-P changes-A .base-term u′ vf vu′
        base-trace P-trace A-trace refl
    | refl , refl
    with eventual-return
      (Return.coerce-problem refl world-agreement W⊢ runtime runtime-env
        p⊢ U⊢ θ-agrees U-agrees P-trace vu′)
complete-apply-blame-after-root {measure = measure}
    {W = W} {U = U} {u = u}
    solver world-agreement W⊢
    (function-proxy-typed {θ = θ} {V = base} {p = p} {q = q}
      W₀⊢ runtime runtime-env environment (C.cast-fun p⊢ q⊢) base⊢)
    U⊢
    (function-proxy-trace-agrees {τ = τ} {v = base-term}
      θ-agrees base-agrees)
    U-agrees root tail tail-smaller | refl , refl
    | active-blames {changes-C = changes-Q}
        vz inner-trace Q-trace refl
    | application-trace-decomposition
        .[] changes-P changes-A .base-term u′ vf vu′
        base-trace P-trace A-trace refl
    | refl , refl | nP , W₁ , U′ , P-eq
    with align-coerce-return {n = nP}
      world-agreement θ-agrees U-agrees P-trace vu′ P-eq
complete-apply-blame-after-root {measure = measure}
    {W = W} {U = U} {u = u}
    solver world-agreement W⊢
    (function-proxy-typed {θ = θ} {V = base} {p = p} {q = q}
      W₀⊢ runtime runtime-env environment (C.cast-fun p⊢ q⊢) base⊢)
    U⊢
    (function-proxy-trace-agrees {τ = τ} {v = base-term}
      θ-agrees base-agrees)
    U-agrees root tail tail-smaller | refl , refl
    | active-blames vz inner-trace Q-trace refl
    | application-trace-decomposition
        .[] changes-P changes-A .base-term u′ vf vu′
        base-trace P-trace A-trace refl
    | refl , refl | nP , W₁ , U′ , P-eq | path-P , U′-agrees
    with coerce-returned-typing nP W⊢ runtime runtime-env p⊢ U⊢ P-eq
complete-apply-blame-after-root {measure = measure}
    {W = W} {U = U} {u = u}
    solver world-agreement W⊢
    (function-proxy-typed {θ = θ} {V = base} {p = p} {q = q}
      W₀⊢ runtime runtime-env environment (C.cast-fun p⊢ q⊢) base⊢)
    U⊢
    (function-proxy-trace-agrees {τ = τ} {v = base-term}
      θ-agrees base-agrees)
    U-agrees root tail tail-smaller | refl , refl
    | active-blames {changes-C = changes-Q}
        vz inner-trace Q-trace refl
    | application-trace-decomposition
        .[] changes-P changes-A .base-term u′ vf vu′
        base-trace P-trace A-trace refl
    | refl , refl | nP , W₁ , U′ , P-eq | path-P , U′-agrees
    | W≤W₁ , W₁⊢ , U′⊢
    with eventual-return
      (Return.apply-problem refl agreement-P W₁⊢
        (value-weaken W≤W₁ W₁⊢ base⊢) U′⊢
        (value-trace-path-empty world-agreement path-P base-agrees)
        U′-agrees A-trace vz)
  where
  agreement-P = world-trace-agreement-++ world-agreement path-P
complete-apply-blame-after-root {measure = measure}
    {W = W} {U = U} {u = u}
    solver world-agreement W⊢
    (function-proxy-typed {θ = θ} {V = base} {p = p} {q = q}
      W₀⊢ runtime runtime-env environment (C.cast-fun p⊢ q⊢) base⊢)
    U⊢
    (function-proxy-trace-agrees {τ = τ} {v = base-term}
      θ-agrees base-agrees)
    U-agrees root tail tail-smaller | refl , refl
    | active-blames {changes-C = changes-Q}
        vz inner-trace Q-trace refl
    | application-trace-decomposition
        .[] changes-P changes-A .base-term u′ vf vu′
        base-trace P-trace A-trace refl
    | refl , refl | nP , W₁ , U′ , P-eq | path-P , U′-agrees
    | W≤W₁ , W₁⊢ , U′⊢ | nA , W₂ , V′ , A-eq
    with align-apply-return {n = nA}
      agreement-P
      (value-trace-path-empty world-agreement path-P base-agrees)
      U′-agrees A-trace vz A-eq
  where
  agreement-P = world-trace-agreement-++ world-agreement path-P
complete-apply-blame-after-root {measure = measure}
    {W = W} {U = U} {u = u}
    solver world-agreement W⊢
    (function-proxy-typed {θ = θ} {V = base} {p = p} {q = q}
      W₀⊢ runtime runtime-env environment (C.cast-fun p⊢ q⊢) base⊢)
    U⊢
    (function-proxy-trace-agrees {τ = τ} {v = base-term}
      θ-agrees base-agrees)
    U-agrees root tail tail-smaller | refl , refl
    | active-blames vz inner-trace Q-trace refl
    | application-trace-decomposition
        .[] changes-P changes-A .base-term u′ vf vu′
        base-trace P-trace A-trace refl
    | refl , refl | nP , W₁ , U′ , P-eq | path-P , U′-agrees
    | W≤W₁ , W₁⊢ , U′⊢ | nA , W₂ , V′ , A-eq
    | path-A , V′-agrees
    with apply-returned-typing nA W₁⊢
      (value-weaken W≤W₁ W₁⊢ base⊢) U′⊢ A-eq
complete-apply-blame-after-root {measure = measure}
    {W = W} {U = U} {u = u}
    solver world-agreement W⊢
    (function-proxy-typed {θ = θ} {V = base} {p = p} {q = q}
      W₀⊢ runtime runtime-env environment (C.cast-fun p⊢ q⊢) base⊢)
    U⊢
    (function-proxy-trace-agrees {τ = τ} {v = base-term}
      θ-agrees base-agrees)
    U-agrees root tail tail-smaller | refl , refl
    | active-blames vz inner-trace Q-trace refl
    | application-trace-decomposition
        .[] changes-P changes-A .base-term u′ vf vu′
        base-trace P-trace A-trace refl
    | refl , refl | nP , W₁ , U′ , P-eq | path-P , U′-agrees
    | W≤W₁ , W₁⊢ , U′⊢ | nA , W₂ , V′ , A-eq
    | path-A , V′-agrees | W₁≤W₂ , W₂⊢ , V′⊢
    with type-environment-trace-path world-agreement
      (world-trace-path-++ path-P path-A) θ-agrees
complete-apply-blame-after-root {measure = measure}
    {W = W} {U = U} {u = u}
    solver world-agreement W⊢
    (function-proxy-typed {θ = θ} {V = base} {p = p} {q = q}
      W₀⊢ runtime runtime-env environment (C.cast-fun p⊢ q⊢) base⊢)
    U⊢
    (function-proxy-trace-agrees {τ = τ} {v = base-term}
      θ-agrees base-agrees)
    U-agrees root tail tail-smaller | refl , refl
    | active-blames {changes-C = changes-Q}
        vz inner-trace Q-trace refl
    | application-trace-decomposition
        .[] changes-P changes-A .base-term u′ vf vu′
        base-trace P-trace A-trace refl
    | refl , refl | nP , W₁ , U′ , P-eq | path-P , U′-agrees
    | W≤W₁ , W₁⊢ , U′⊢ | nA , W₂ , V′ , A-eq
    | path-A , V′-agrees | W₁≤W₂ , W₂⊢ , V′⊢
    | path-agreement
    with solver Q-smaller
      (coerce-problem refl agreement-PA W₂⊢
        (runtime-context-weaken
          (world-extension-trans W≤W₁ W₁≤W₂) runtime)
        runtime-env q⊢ V′⊢
        (type-environment-trace-rebase
          (final-agreement path-agreement)) V′-agrees Q-trace′)
  where
  agreement-P = world-trace-agreement-++ world-agreement path-P
  agreement-PA = world-trace-agreement-++ agreement-P path-A
  Q-smaller : length changes-Q < measure
  Q-smaller = ≤-<-trans
    (suffix-length≤ (changes-P ++ changes-A) changes-Q)
    tail-smaller
  Q-trace′ = subst
    (λ d → _ N.⟨ d ⟩ —↠[ _ ] N.blame)
    (sym (coercion-action path-agreement q)) Q-trace
complete-apply-blame-after-root {W = W} {U = U} {u = u}
    solver world-agreement W⊢
    (function-proxy-typed {θ = θ} {V = base} {p = p} {q = q}
      W₀⊢ runtime runtime-env environment (C.cast-fun p⊢ q⊢) base⊢)
    U⊢
    (function-proxy-trace-agrees {τ = τ} {v = base-term}
      θ-agrees base-agrees)
    U-agrees root tail tail-smaller | refl , refl
    | active-blames vz inner-trace Q-trace refl
    | application-trace-decomposition
        .[] changes-P changes-A .base-term u′ vf vu′
        base-trace P-trace A-trace refl
    | refl , refl | nP , W₁ , U′ , P-eq | path-P , U′-agrees
    | W≤W₁ , W₁⊢ , U′⊢ | nA , W₂ , V′ , A-eq
    | path-A , V′-agrees | W₁≤W₂ , W₂⊢ , V′⊢
    | path-agreement | nQ , Z , Q-eq =
  suc (nP + (nA + nQ)) , Z , apply-proxy-from-result-blame
    {W = W} {p = p} {q = q} {θ = θ} {V = base} {U = U}
    {nP = nP} {W₁ = W₁} {U′ = U′}
    {nA = nA} {W₂ = W₂} {V′ = V′}
    {nQ = nQ} {Z = Z} P-eq A-eq Q-eq

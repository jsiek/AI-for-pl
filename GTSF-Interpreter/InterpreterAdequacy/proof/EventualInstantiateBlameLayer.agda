module InterpreterAdequacy.proof.EventualInstantiateBlameLayer where

-- File Charter:
--   * Constructs finite blamed `instantiateValue` runs after one bullet root.
--   * Splits forall proxies into inner instantiation and coercion phases.
--   * Uses return completeness for the successful inner phase and blame
--     recursion only for a strictly shorter blamed phase.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Data.List using ([]; _++_; length; map)
open import Data.Maybe using (just)
open import Data.Nat using (_+_; _<_; suc)
open import Data.Nat.Properties using (<-trans; ≤-<-trans)
open import Data.Product using (_,_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)

import Coercions as C
open import Interpreter
open import InterpreterAdequacy.TraceAgreement
open import InterpreterAdequacy.proof.CastBlameTraceDecomposition
open import InterpreterAdequacy.proof.EventualBlameProblem
open import InterpreterAdequacy.proof.EventualReturnAlignment using
  (align-instantiate-return)
import InterpreterAdequacy.proof.EventualReturnProblem as Return
open import InterpreterAdequacy.proof.EventualReturnDriver using
  (eventual-return)
open import InterpreterAdequacy.proof.EventualReturnTyping using
  (instantiate-returned-typing)
open import InterpreterAdequacy.proof.FiniteRunComposition using
  ( instantiate-forall-from-coercion-blame
  ; instantiate-forall-from-inner-blame
  ; instantiate-generalized-from-coercion-blame
  )
open import InterpreterAdequacy.proof.TraceAgreementPath using
  (type-environment-trace-rebase)
open import InterpreterAdequacy.proof.TraceAgreementProperties using
  (world-trace-agreement-++)
open import InterpreterAdequacy.proof.TraceMeasure using
  (prefix-before-step-shorter; suffix-length≤)
open import InterpreterAdequacy.proof.TypeAbstractionBetaReification using
  (open-extended-coercion)
open import InterpreterAdequacy.proof.TypeAbstractionInstantiationSoundness
  using (type-environment-instantiate-head)
open import InterpreterAdequacy.proof.TypeEnvironmentTracePath
open import Typing.InterpreterSemanticTypingCore
open import Narrowing.InterpreterWorldNarrowing using (Allocated; seal-scoped)
open import NuReduction
import NuTerms as N
open import proof.DGG.Core.NuReductionDeterminism using
  (source-blame-excludes-value)
open import proof.Core.Properties.NuTermProperties using
  (renameᵗᵐ-preserves-Value)
open import proof.InterpreterSemanticTypingProperties using
  ( allocated-weaken
  ; interpret-weaken
  ; instantiate-interpret
  ; runtime-context-name
  ; runtime-context-weaken
  )
open import proof.InterpreterTypingCore using (coerceValue-typing)
open import proof.Core.Properties.ReductionProperties using
  (applyCoercions)

complete-instantiate-blame-after-root :
  ∀ {measure W prefix α F f A} →
  StrictlySmallerBlameSolver measure →
  (world-agreement : WorldTraceAgreement W prefix) →
  (W⊢ : WorldTyping W) →
  (allocated-ok : Allocated W α) →
  (F⊢ : ValueTyping W F (polymorphic-type A)) →
  (newest :
    lookup (visibleTypeNames [] W) 0 ≡ just (seal-name α)) →
  (F-agrees : ValueTraceAgreement world-agreement [] F f) →
  ∀ {tail next} →
  (f N.•) —→[ keep ] next →
  next —↠[ tail ] N.blame →
  length tail < measure →
  Σ[ n ∈ StepIndex ]
  Σ[ Z ∈ World ] instantiateValue W α F n ≡ blamed Z

complete-instantiate-blame-after-root {W = W}
    solver world-agreement W⊢ allocated-ok
    (type-abstraction-typed
      W₀⊢ runtime runtime-env environment fresh graph image body⊢)
    newest
    (type-abstraction-trace-agrees
      fresh′ graph′ θ-agrees γ-agrees no-raw reification vP no-P)
    (pure-step (β-Λ• vF)) tail tail-smaller =
  ⊥-elim
    (source-blame-excludes-value tail ↠-refl
      (renameᵗᵐ-preserves-Value _ vF))

complete-instantiate-blame-after-root {measure = measure}
    {W = W} {α = α} {F = forall-proxy c θ V}
    solver world-agreement W⊢ allocated-ok
    (forall-proxy-typed {A = body-A}
      W₀⊢ runtime runtime-env environment (C.cast-all c⊢) base⊢)
    newest
    (forall-proxy-trace-agrees {τ = τ} θ-agrees base-agrees)
    (pure-step (β-∀• vBase)) tail tail-smaller
    with decompose-cast-blame-trace tail
complete-instantiate-blame-after-root {measure = measure}
    {W = W} {α = α} {F = forall-proxy c θ V}
    solver world-agreement W⊢ allocated-ok
    (forall-proxy-typed {A = body-A}
      W₀⊢ runtime runtime-env environment (C.cast-all c⊢) base⊢)
    newest
    (forall-proxy-trace-agrees {τ = τ} θ-agrees base-agrees)
    (pure-step (β-∀• vBase)) tail tail-smaller
    | operand-blames {changes-M = changes-I} I-trace refl
    with solver I-smaller
      (instantiate-problem refl world-agreement W⊢ allocated-ok base⊢
        newest base-agrees I-trace)
  where
  I-smaller : length changes-I < measure
  I-smaller = <-trans
    (prefix-before-step-shorter changes-I [] keep) tail-smaller
complete-instantiate-blame-after-root {W = W} {α = α}
    {F = forall-proxy c θ V}
    solver world-agreement W⊢ allocated-ok
    (forall-proxy-typed W₀⊢ runtime runtime-env environment c⊢ base⊢)
    newest (forall-proxy-trace-agrees θ-agrees base-agrees)
    (pure-step (β-∀• vBase)) tail tail-smaller
    | operand-blames I-trace refl | nI , Z , I-eq =
  suc nI , Z , instantiate-forall-from-inner-blame
    {W = W} {α = α} {c = c} {θ = θ} {V = V}
    {n = nI} {Z = Z} I-eq

complete-instantiate-blame-after-root {measure = measure}
    {W = W} {α = α} {F = forall-proxy c θ V}
    solver world-agreement W⊢ allocated-ok
    (forall-proxy-typed {A = body-A}
      W₀⊢ runtime runtime-env environment (C.cast-all c⊢) base⊢)
    newest
    (forall-proxy-trace-agrees {τ = τ} θ-agrees base-agrees)
    (pure-step (β-∀• vBase)) tail tail-smaller
    | active-blames {changes-M = changes-I}
        {changes-C = changes-C} {u = u} vu I-trace C-trace refl
    with eventual-return
      (Return.instantiate-problem refl world-agreement W⊢ allocated-ok
        base⊢ newest base-agrees I-trace vu)
complete-instantiate-blame-after-root {measure = measure}
    {W = W} {α = α} {F = forall-proxy c θ V}
    solver world-agreement W⊢ allocated-ok
    (forall-proxy-typed {A = body-A}
      W₀⊢ runtime runtime-env environment (C.cast-all c⊢) base⊢)
    newest
    (forall-proxy-trace-agrees {τ = τ} θ-agrees base-agrees)
    (pure-step (β-∀• vBase)) tail tail-smaller
    | active-blames {changes-M = changes-I}
        {changes-C = changes-C} {u = u} vu I-trace C-trace refl
    | nI , W₁ , U , I-eq
    with align-instantiate-return {n = nI} {changes = changes-I}
      world-agreement newest base-agrees I-trace vu I-eq
complete-instantiate-blame-after-root {measure = measure}
    {W = W} {α = α} {F = forall-proxy c θ V}
    solver world-agreement W⊢ allocated-ok
    (forall-proxy-typed {A = body-A}
      W₀⊢ runtime runtime-env environment (C.cast-all c⊢) base⊢)
    newest
    (forall-proxy-trace-agrees {τ = τ} θ-agrees base-agrees)
    (pure-step (β-∀• vBase)) tail tail-smaller
    | active-blames {changes-M = changes-I}
        {changes-C = changes-C} {u = u} vu I-trace C-trace refl
    | nI , W₁ , U , I-eq | path-I , U-agrees
    with instantiate-returned-typing nI W⊢ allocated-ok base⊢ I-eq
complete-instantiate-blame-after-root {measure = measure}
    {W = W} {α = α} {F = forall-proxy c θ V}
    solver world-agreement W⊢ allocated-ok
    (forall-proxy-typed {A = body-A}
      W₀⊢ runtime runtime-env environment (C.cast-all c⊢) base⊢)
    newest
    (forall-proxy-trace-agrees {τ = τ} θ-agrees base-agrees)
    (pure-step (β-∀• vBase)) tail tail-smaller
    | active-blames {changes-M = changes-I}
        {changes-C = changes-C} {u = u} vu I-trace C-trace refl
    | nI , W₁ , U , I-eq | path-I , U-agrees
    | W≤W₁ , W₁⊢ , U⊢
    with type-environment-trace-path world-agreement path-I
      extended-agreement
  where
  extended-agreement =
    type-environment-instantiate-head newest θ-agrees
complete-instantiate-blame-after-root {measure = measure}
    {W = W} {α = α} {F = forall-proxy c θ V}
    solver world-agreement W⊢ allocated-ok
    (forall-proxy-typed {A = body-A}
      W₀⊢ runtime runtime-env environment (C.cast-all c⊢) base⊢)
    newest
    (forall-proxy-trace-agrees {τ = τ} θ-agrees base-agrees)
    (pure-step (β-∀• vBase)) tail tail-smaller
    | active-blames {changes-M = changes-I}
        {changes-C = changes-C} {u = u} vu I-trace C-trace refl
    | nI , W₁ , U , I-eq | path-I , U-agrees
    | W≤W₁ , W₁⊢ , U⊢ | path-agreement
    with solver C-smaller
      (coerce-problem refl agreement-I W₁⊢
        (runtime-context-name
          (seal-scoped (allocated-weaken W≤W₁ allocated-ok))
          (runtime-context-weaken W≤W₁ runtime))
        (runtime-type-seal runtime-env) c⊢
        (subst (ValueTyping W₁ U)
          (instantiate-interpret
            (nominal-type (seal-name α)) _ body-A) U⊢)
        (type-environment-trace-rebase
          (final-agreement path-agreement))
        U-agrees C-trace′)
  where
  agreement-I = world-trace-agreement-++ world-agreement path-I
  extended-agreement =
    type-environment-instantiate-head newest θ-agrees
  C-smaller : length changes-C < measure
  C-smaller = ≤-<-trans
    (suffix-length≤ changes-I changes-C) tail-smaller
  final-eq = trans (coercion-action path-agreement c)
    (cong (applyCoercions changes-I)
      (sym (open-extended-coercion τ c)))
  C-trace′ = subst
    (λ d → u N.⟨ d ⟩ —↠[ changes-C ] N.blame)
    (sym final-eq) C-trace
complete-instantiate-blame-after-root {W = W} {α = α}
    {F = forall-proxy c θ V}
    solver world-agreement W⊢ allocated-ok
    (forall-proxy-typed W₀⊢ runtime runtime-env environment c⊢ base⊢)
    newest (forall-proxy-trace-agrees θ-agrees base-agrees)
    (pure-step (β-∀• vBase)) tail tail-smaller
    | active-blames {changes-M = changes-I}
        {changes-C = changes-C} {u = u} vu I-trace C-trace refl
    | nI , W₁ , U , I-eq | path-I , U-agrees
    | W≤W₁ , W₁⊢ , U⊢ | path-agreement
    | nC , Z , C-eq =
  suc (nI + nC) , Z , instantiate-forall-from-coercion-blame
    {W = W} {α = α} {c = c} {θ = θ} {V = V}
    {nI = nI} {W₁ = W₁} {U = U} {nC = nC}
    I-eq C-eq

complete-instantiate-blame-after-root {measure = measure}
    {W = W} {α = α} {F = generalized source-A c θ V}
    solver world-agreement W⊢ allocated-ok
    (generalized-typed {A = source-A}
      W₀⊢ runtime runtime-env environment
      (C.cast-gen hA occurs c⊢) base⊢)
    newest
    (generalized-trace-agrees {τ = τ} θ-agrees base-agrees)
    (pure-step (β-gen• vBase)) tail tail-smaller
    with solver tail-smaller
      (coerce-problem refl world-agreement W⊢
        (runtime-context-name (seal-scoped allocated-ok) runtime)
        (runtime-type-seal runtime-env) c⊢
        (subst (ValueTyping W _)
          (sym (interpret-weaken
            (nominal-type (seal-name α))
            (semanticEnvironment _) source-A))
          base⊢)
        extended-agreement base-agrees tail′)
  where
  extended-agreement =
    type-environment-instantiate-head newest θ-agrees
  tail′ = subst
    (λ d → _ N.⟨ d ⟩ —↠[ _ ] N.blame)
    (open-extended-coercion τ c) tail
complete-instantiate-blame-after-root {W = W} {α = α}
    {F = generalized source-A c θ V}
    solver world-agreement W⊢ allocated-ok
    (generalized-typed W₀⊢ runtime runtime-env environment c⊢ base⊢)
    newest (generalized-trace-agrees θ-agrees base-agrees)
    (pure-step (β-gen• vBase)) tail tail-smaller
    | nC , Z , C-eq =
  suc nC , Z , instantiate-generalized-from-coercion-blame
    {W = W} {α = α} {A = source-A} {c = c} {θ = θ} {V = V}
    {n = nC} {Z = Z} C-eq

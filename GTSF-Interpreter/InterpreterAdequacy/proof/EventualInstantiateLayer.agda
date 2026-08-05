module InterpreterAdequacy.proof.EventualInstantiateLayer where

-- File Charter:
--   * Constructs a finite `instantiateValue` return after consuming one
--     small-step bullet root.
--   * Handles abstractions immediately and splits forall proxies into a
--     smaller instantiation followed by a smaller coercion.
--   * Reuses the allocated seal as the head runtime type name for forall and
--     generalized coercion bodies.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _++_; length; map)
open import Data.Maybe using (just)
open import Data.Nat using (_+_; _<_; suc; zero)
open import Data.Nat.Properties using (≤-<-trans)
open import Data.Product using (_,_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)

import Coercions as C
open import Interpreter
open import InterpreterAdequacy.TraceAgreement
open import InterpreterAdequacy.proof.CastTraceDecomposition
open import InterpreterAdequacy.proof.EventualReturnAlignment using
  (align-instantiate-return)
open import InterpreterAdequacy.proof.EventualReturnProblem
open import InterpreterAdequacy.proof.EventualReturnTyping using
  (instantiate-returned-typing)
open import InterpreterAdequacy.proof.FiniteRunComposition using
  (instantiate-forall-from-phases)
open import InterpreterAdequacy.proof.TraceAgreementPath using
  (type-environment-trace-rebase)
open import InterpreterAdequacy.proof.TraceAgreementProperties using
  (world-trace-agreement-++)
open import InterpreterAdequacy.proof.TraceMeasure using
  (prefix-length≤; suffix-length≤)
open import InterpreterAdequacy.proof.TypeAbstractionBetaReification using
  (extend-after-opening; open-extended-coercion)
open import InterpreterAdequacy.proof.TypeAbstractionInstantiationSoundness
  using (type-environment-instantiate-head)
open import InterpreterAdequacy.proof.TypeEnvironmentTracePath
open import Typing.InterpreterSemanticTypingCore
open import Narrowing.InterpreterWorldNarrowing using (Allocated; seal-scoped)
open import NuReduction
import NuTerms as N
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

complete-instantiate-after-root :
  ∀ {measure W prefix α F f A v} →
  StrictlySmallerSolver measure →
  (world-agreement : WorldTraceAgreement W prefix) →
  (W⊢ : WorldTyping W) →
  (allocated : Allocated W α) →
  (F⊢ : ValueTyping W F (polymorphic-type A)) →
  (newest :
    lookup (visibleTypeNames [] W) zero ≡ just (seal-name α)) →
  (F-agrees : ValueTraceAgreement world-agreement [] F f) →
  ∀ {tail next} →
  (f N.•) —→[ keep ] next →
  next —↠[ tail ] v →
  N.Value v →
  length tail < measure →
  Σ[ n ∈ StepIndex ]
  Σ[ Z ∈ World ]
  Σ[ R ∈ Value ]
    (instantiateValue W α F n ≡ returned Z R)

complete-instantiate-after-root {W = W}
    solver world-agreement W⊢ allocated
    (type-abstraction-typed
      W₀⊢ runtime runtime-env environment fresh graph image body⊢)
    newest
    (type-abstraction-trace-agrees
      fresh′ graph′ θ-agrees γ-agrees no-raw reification vP no-P)
    (pure-step (β-Λ• vF)) tail vV tail-smaller =
  suc zero , _ , _ , refl

complete-instantiate-after-root {W = W} {α = α}
    {F = forall-proxy c θ V}
    solver world-agreement W⊢ allocated
    (forall-proxy-typed {A = body-A}
      W₀⊢ runtime runtime-env environment
      (C.cast-all c⊢) base⊢)
    newest
    (forall-proxy-trace-agrees {τ = τ}
      θ-agrees base-agrees)
    (pure-step (β-∀• vBase)) tail vV tail-smaller
    with decompose-cast-value-trace tail vV
complete-instantiate-after-root {W = W} {α = α}
    {F = forall-proxy c θ V}
    solver world-agreement W⊢ allocated
    (forall-proxy-typed {A = body-A}
      W₀⊢ runtime runtime-env environment
      (C.cast-all c⊢) base⊢)
    newest
    (forall-proxy-trace-agrees {τ = τ}
      θ-agrees base-agrees)
    (pure-step (β-∀• vBase)) tail vV tail-smaller
    | cast-trace-decomposition
        changes-I changes-C u vu I-trace C-trace refl
    with solver I-smaller
      (instantiate-problem refl world-agreement W⊢ allocated base⊢
        newest base-agrees I-trace vu)
  where
  I-smaller : length changes-I < _
  I-smaller = ≤-<-trans
    (prefix-length≤ changes-I changes-C) tail-smaller
complete-instantiate-after-root {F = forall-proxy c θ V}
    solver world-agreement W⊢ allocated
    (forall-proxy-typed {A = body-A}
      W₀⊢ runtime runtime-env environment
      (C.cast-all c⊢) base⊢)
    newest
    (forall-proxy-trace-agrees {τ = τ}
      θ-agrees base-agrees)
    (pure-step (β-∀• vBase)) tail vV tail-smaller
    | cast-trace-decomposition
        changes-I changes-C u vu I-trace C-trace refl
    | nI , W₁ , U , I-eq
    with align-instantiate-return {n = nI} {changes = changes-I}
      world-agreement newest base-agrees I-trace vu I-eq
complete-instantiate-after-root {F = forall-proxy c θ V}
    solver world-agreement W⊢ allocated
    (forall-proxy-typed {A = body-A}
      W₀⊢ runtime runtime-env environment
      (C.cast-all c⊢) base⊢)
    newest
    (forall-proxy-trace-agrees {τ = τ}
      θ-agrees base-agrees)
    (pure-step (β-∀• vBase)) tail vV tail-smaller
    | cast-trace-decomposition
        changes-I changes-C u vu I-trace C-trace refl
    | nI , W₁ , U , I-eq | path-I , U-agrees
    with instantiate-returned-typing nI W⊢ allocated base⊢ I-eq
complete-instantiate-after-root {F = forall-proxy c θ V}
    solver world-agreement W⊢ allocated
    (forall-proxy-typed {A = body-A}
      W₀⊢ runtime runtime-env environment
      (C.cast-all c⊢) base⊢)
    newest
    (forall-proxy-trace-agrees {τ = τ}
      θ-agrees base-agrees)
    (pure-step (β-∀• vBase)) tail vV tail-smaller
    | cast-trace-decomposition
        changes-I changes-C u vu I-trace C-trace refl
    | nI , W₁ , U , I-eq | path-I , U-agrees
    | W≤W₁ , W₁⊢ , U⊢
    with type-environment-trace-path world-agreement path-I
      extended-agreement
  where
  extended-agreement =
    type-environment-instantiate-head newest θ-agrees
complete-instantiate-after-root {F = forall-proxy c θ V}
    solver world-agreement W⊢ allocated
    (forall-proxy-typed {A = body-A}
      W₀⊢ runtime runtime-env environment
      (C.cast-all c⊢) base⊢)
    newest
    (forall-proxy-trace-agrees {τ = τ}
      θ-agrees base-agrees)
    (pure-step (β-∀• vBase)) tail vV tail-smaller
    | cast-trace-decomposition
        changes-I changes-C u vu I-trace C-trace refl
    | nI , W₁ , U , I-eq | path-I , U-agrees
    | W≤W₁ , W₁⊢ , U⊢
    | path-agreement
    with solver C-smaller
      (coerce-problem refl agreement-I W₁⊢
        (runtime-context-name
          (seal-scoped (allocated-weaken W≤W₁ allocated))
          (runtime-context-weaken W≤W₁ runtime))
        (runtime-type-seal runtime-env) c⊢
        (subst (ValueTyping W₁ U)
          (instantiate-interpret
            (nominal-type (seal-name _)) _ body-A)
          U⊢)
        (type-environment-trace-rebase
          (final-agreement path-agreement))
        U-agrees C-trace′ vV)
  where
  agreement-I = world-trace-agreement-++ world-agreement path-I
  extended-agreement =
    type-environment-instantiate-head newest θ-agrees
  C-smaller : length changes-C < _
  C-smaller = ≤-<-trans
    (suffix-length≤ changes-I changes-C) tail-smaller
  opened-eq = open-extended-coercion τ c
  final-eq = trans (coercion-action path-agreement c)
    (cong (applyCoercions changes-I)
      (sym opened-eq))
  C-trace′ = subst
    (\ d → u N.⟨ d ⟩ —↠[ changes-C ] _)
    (sym final-eq) C-trace
complete-instantiate-after-root {W = W} {α = α}
    {F = forall-proxy c θ V}
    solver world-agreement W⊢ allocated
    (forall-proxy-typed {A = body-A}
      W₀⊢ runtime runtime-env environment
      (C.cast-all c⊢) base⊢)
    newest
    (forall-proxy-trace-agrees {τ = τ}
      θ-agrees base-agrees)
    (pure-step (β-∀• vBase)) tail vV tail-smaller
    | cast-trace-decomposition
        changes-I changes-C u vu I-trace C-trace refl
    | nI , W₁ , U , I-eq | path-I , U-agrees
    | W≤W₁ , W₁⊢ , U⊢
    | path-agreement | nC , W₂ , R , C-eq =
  suc (nI + nC) , W₂ , R ,
    instantiate-forall-from-phases
      {W = W} {α = α} {c = c} {θ = θ} {V = V}
      {nI = nI} {W₁ = W₁} {U = U}
      {nC = nC} {W₂ = W₂} {R = R} I-eq C-eq

complete-instantiate-after-root {W = W}
    {F = generalized source-A c θ V}
    solver world-agreement W⊢ allocated
    (generalized-typed {A = source-A}
      W₀⊢ runtime runtime-env environment
      (C.cast-gen hA occurs c⊢) base⊢)
    newest
    (generalized-trace-agrees {τ = τ}
      θ-agrees base-agrees)
    (pure-step (β-gen• vBase)) tail vV tail-smaller
    with solver tail-smaller
      (coerce-problem refl world-agreement W⊢
        (runtime-context-name (seal-scoped allocated) runtime)
        (runtime-type-seal runtime-env) c⊢
        (subst (ValueTyping W _)
          (sym (interpret-weaken
            (nominal-type (seal-name _))
            (semanticEnvironment _) source-A))
          base⊢)
        extended-agreement base-agrees tail′ vV)
  where
  extended-agreement =
    type-environment-instantiate-head newest θ-agrees
  tail′ = subst
    (\ d → _ N.⟨ d ⟩ —↠[ _ ] _)
    (open-extended-coercion τ c) tail
complete-instantiate-after-root {F = generalized source-A c θ V}
    solver world-agreement W⊢ allocated
    (generalized-typed W₀⊢ runtime runtime-env environment c⊢ base⊢)
    newest
    (generalized-trace-agrees θ-agrees base-agrees)
    (pure-step (β-gen• vBase)) tail vV tail-smaller
    | nC , W₁ , R , C-eq =
  suc nC , W₁ , R , C-eq

module InterpreterAdequacy.proof.EventualCoerceLayer where

-- File Charter:
--   * Constructs finite `coerceValue` returns from terminating cast traces.
--   * Splits sequence and instantiation roots into strictly shorter trace
--     phases and handles inert casts without recursion.
--   * Uses concrete blame exclusion only against the supplied value trace.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Data.List using ([]; _∷_; _++_; length)
open import Data.Maybe using (just)
open import Data.Nat using (_+_; _<_; _≤_; suc; zero)
open import Data.Nat.Properties using (n≤1+n; ≤-<-trans; ≤-trans)
open import Data.Product using (_,_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)

import Coercions as C
open import Interpreter
open import InterpreterAdequacy.TraceAgreement
open import InterpreterAdequacy.proof.AllocationTrace using
  (allocation-path)
open import InterpreterAdequacy.proof.ApplicationTraceDecomposition using
  (blame-does-not-reach-value)
open import InterpreterAdequacy.proof.CastTraceDecomposition
open import InterpreterAdequacy.proof.EventualReturnAlignment using
  (align-coerce-return; align-instantiate-return)
open import InterpreterAdequacy.proof.EventualReturnProblem
open import InterpreterAdequacy.proof.EventualReturnTyping using
  (coerce-returned-typing; instantiate-returned-typing)
open import InterpreterAdequacy.proof.FiniteRunComposition using
  (coerce-instantiation-from-phases; coerce-sequence-from-phases)
open import InterpreterAdequacy.proof.ImmediateCoercionCompleteness using
  (complete-immediate-coercion)
open import InterpreterAdequacy.proof.ImmediateCoercionTermination using
  (unseal-positive-not-timed; untag-positive-not-timed)
open import InterpreterAdequacy.proof.InterpreterValueCompleteness using
  (execute-inert-frame-local; rename-inert-reflect)
open import InterpreterAdequacy.proof.NuTraceDecomposition using
  (nu-value-tail)
open import InterpreterAdequacy.proof.TraceAgreementBind using
  (new-seal-lookup; type-environment-trace-bind)
open import InterpreterAdequacy.proof.TraceAgreementPath using
  (type-environment-trace-rebase; value-trace-path-empty)
open import InterpreterAdequacy.proof.TraceAgreementProperties using
  (value-trace-no-bullet; value-trace-value; world-trace-agreement-++)
open import InterpreterAdequacy.proof.TraceMeasure using
  (prefix-length≤; suffix-length≤)
open import InterpreterAdequacy.proof.TypeAbstractionBetaReification using
  (extend-after-insertion)
open import InterpreterAdequacy.proof.TypeAbstractionInstantiationSoundness
  using (type-environment-instantiate-head)
open import InterpreterAdequacy.proof.TypeEnvironmentTracePath
open import Runtime.InterpreterInertFrameCore using
  (InertFrameExecution; computes; result)
open import Typing.InterpreterSemanticTypingCore
open import Narrowing.InterpreterWorldNarrowing using (Allocated)
open import NuReduction
import NuTerms as N
open import proof.Core.Properties.CoercionProperties using
  (renameᶜ-cong)
open import proof.Core.Properties.ReductionProperties using
  (applyCoercions)
open import proof.DGG.Core.NuReductionDeterminism using
  (value-irreducible)
open import proof.InterpreterSemanticTypingProperties using
  ( allocated-here
  ; instantiate-interpret
  ; runtime-context-seal
  ; runtime-context-weaken
  ; value-weaken
  )
open import Types using (★; wf★)

complete-coerce-refl :
  ∀ {W prefix Δ Σ θ τ c V u A B μ} →
  (world-agreement : WorldTraceAgreement W prefix) →
  WorldTyping W →
  (runtime : RuntimeContext W Δ Σ θ) →
  (runtime-env : RuntimeTypeEnvironment θ) →
  C._∣_∣_⊢_∶_=⇒_ μ Δ Σ c A B →
  ValueTyping W V ⟦ A ⟧[ θ ] →
  TypeEnvironmentTraceAgreement world-agreement [] θ τ →
  ValueTraceAgreement world-agreement [] V u →
  N.Value (u N.⟨ C.renameᶜ τ c ⟩) →
  Σ[ n ∈ StepIndex ]
  Σ[ Z ∈ World ]
  Σ[ R ∈ Value ] coerceValue W θ c V n ≡ returned Z R
complete-coerce-refl world-agreement W⊢ runtime runtime-env c⊢ V⊢
    θ-agrees V-agrees (vu N.⟨ inert ⟩)
    with execute-inert-frame-local runtime runtime-env c⊢
      (rename-inert-reflect _ inert)
complete-coerce-refl world-agreement W⊢ runtime runtime-env c⊢ V⊢
    θ-agrees V-agrees (vu N.⟨ inert ⟩) | execution =
  suc zero , _ , result execution , computes execution zero

complete-coerce-after-root :
  ∀ {measure W prefix Δ Σ θ τ c V u A B μ v} →
  StrictlySmallerSolver measure →
  (world-agreement : WorldTraceAgreement W prefix) →
  (W⊢ : WorldTyping W) →
  (runtime : RuntimeContext W Δ Σ θ) →
  (runtime-env : RuntimeTypeEnvironment θ) →
  (c⊢ : C._∣_∣_⊢_∶_=⇒_ μ Δ Σ c A B) →
  (V⊢ : ValueTyping W V ⟦ A ⟧[ θ ]) →
  (θ-agrees : TypeEnvironmentTraceAgreement world-agreement [] θ τ) →
  (V-agrees : ValueTraceAgreement world-agreement [] V u) →
  ∀ {change tail next} →
  (u N.⟨ C.renameᶜ τ c ⟩) —→[ change ] next →
  next —↠[ tail ] v →
  N.Value v →
  length tail < measure →
  Σ[ n ∈ StepIndex ]
  Σ[ Z ∈ World ]
  Σ[ R ∈ Value ] coerceValue W θ c V n ≡ returned Z R

complete-coerce-after-root solver world-agreement W⊢ runtime runtime-env
    (C.cast-id hA allowed) V⊢ θ-agrees V-agrees
    (pure-step (β-id vu)) tail vV tail-smaller =
  suc zero , _ , _ , refl

complete-coerce-after-root solver world-agreement W⊢ runtime runtime-env
    (C.cast-seq c⊢ d⊢) V⊢ θ-agrees V-agrees
    (pure-step (β-seq vu)) tail vV tail-smaller
    with decompose-cast-value-trace tail vV
complete-coerce-after-root solver world-agreement W⊢ runtime runtime-env
    (C.cast-seq c⊢ d⊢) V⊢ θ-agrees V-agrees
    (pure-step (β-seq vu)) tail vV tail-smaller
    | cast-trace-decomposition changes-C changes-D u₁ vu₁
        C-trace D-trace refl
    with solver C-smaller
      (coerce-problem refl world-agreement W⊢ runtime runtime-env c⊢ V⊢
        θ-agrees V-agrees C-trace vu₁)
  where
  C-smaller : length changes-C < _
  C-smaller = ≤-<-trans
    (prefix-length≤ changes-C changes-D) tail-smaller
complete-coerce-after-root solver world-agreement W⊢ runtime runtime-env
    (C.cast-seq c⊢ d⊢) V⊢ θ-agrees V-agrees
    (pure-step (β-seq vu)) tail vV tail-smaller
    | cast-trace-decomposition changes-C changes-D u₁ vu₁
        C-trace D-trace refl
    | nC , W₁ , U , C-eq
    with align-coerce-return {n = nC} {changes = changes-C}
      world-agreement θ-agrees V-agrees C-trace vu₁ C-eq
complete-coerce-after-root {W = W} {θ = θ}
    {c = c C.︔ d} {V = V}
    solver world-agreement W⊢ runtime runtime-env
    (C.cast-seq c⊢ d⊢) V⊢ θ-agrees V-agrees
    (pure-step (β-seq vu)) tail vV tail-smaller
    | cast-trace-decomposition changes-C changes-D u₁ vu₁
        C-trace D-trace refl
    | nC , W₁ , U , C-eq | path-C , U-agrees
    with coerce-returned-typing nC W⊢ runtime runtime-env c⊢ V⊢ C-eq
complete-coerce-after-root solver world-agreement W⊢ runtime runtime-env
    (C.cast-seq c⊢ d⊢) V⊢ θ-agrees V-agrees
    (pure-step (β-seq vu)) tail vV tail-smaller
    | cast-trace-decomposition changes-C changes-D u₁ vu₁
        C-trace D-trace refl
    | nC , W₁ , U , C-eq | path-C , U-agrees
    | W≤W₁ , W₁⊢ , U⊢
    with type-environment-trace-path world-agreement path-C θ-agrees
complete-coerce-after-root solver world-agreement W⊢ runtime runtime-env
    (C.cast-seq c⊢ d⊢) V⊢ θ-agrees V-agrees
    (pure-step (β-seq vu)) tail vV tail-smaller
    | cast-trace-decomposition changes-C changes-D u₁ vu₁
        C-trace D-trace refl
    | nC , W₁ , U , C-eq | path-C , U-agrees
    | W≤W₁ , W₁⊢ , U⊢ | path-agreement
    with solver D-smaller
      (coerce-problem refl agreement-C W₁⊢
        (runtime-context-weaken W≤W₁ runtime) runtime-env d⊢ U⊢
        (type-environment-trace-rebase
          (final-agreement path-agreement)) U-agrees D-trace′ vV)
  where
  agreement-C = world-trace-agreement-++ world-agreement path-C
  D-smaller : length changes-D < _
  D-smaller = ≤-<-trans
    (suffix-length≤ changes-C changes-D) tail-smaller
  D-trace′ = subst
    (\ d → u₁ N.⟨ d ⟩ —↠[ changes-D ] _)
    (sym (coercion-action path-agreement _)) D-trace
complete-coerce-after-root {W = W} {θ = θ}
    {c = c C.︔ d} {V = V}
    solver world-agreement W⊢ runtime runtime-env
    (C.cast-seq c⊢ d⊢) V⊢ θ-agrees V-agrees
    (pure-step (β-seq vu)) tail vV tail-smaller
    | cast-trace-decomposition changes-C changes-D u₁ vu₁
        C-trace D-trace refl
    | nC , W₁ , U , C-eq | path-C , U-agrees
    | W≤W₁ , W₁⊢ , U⊢ | path-agreement
    | nD , W₂ , R , D-eq =
  suc (nC + nD) , W₂ , R ,
    coerce-sequence-from-phases
      {W = W} {θ = θ} {c = c} {d = d} {V = V}
      {nC = nC} {W₁ = W₁} {U = U}
      {nD = nD} {W₂ = W₂} {R = R} C-eq D-eq

complete-coerce-after-root {W = W} {θ = θ} {c = H C.？} {V = V}
    solver world-agreement W⊢ runtime runtime-env
    c⊢@(C.cast-untag hG gG allowed) V⊢ θ-agrees V-agrees
    (pure-step (tag-untag-ok vu)) tail vV tail-smaller =
  complete-immediate-coercion world-agreement W⊢ runtime runtime-env
    c⊢ V⊢ θ-agrees V-agrees
    (↠-step (pure-step (tag-untag-ok vu)) tail) vV
    (untag-positive-not-timed
      {W = W} {θ = θ} {G = H} {V = V} {n = zero})
complete-coerce-after-root solver world-agreement W⊢ runtime runtime-env
    (C.cast-untag hG gG allowed) V⊢ θ-agrees V-agrees
    (pure-step (tag-untag-bad vu G≢H)) tail vV tail-smaller =
  ⊥-elim (blame-does-not-reach-value tail vV)

complete-coerce-after-root {W = W} {θ = θ}
    {c = C.unseal X A} {V = V}
    solver world-agreement W⊢ runtime runtime-env
    c⊢@(C.cast-unseal hA X∈ allowed) V⊢ θ-agrees V-agrees
    (pure-step (seal-unseal vu)) tail vV tail-smaller =
  complete-immediate-coercion world-agreement W⊢ runtime runtime-env
    c⊢ V⊢ θ-agrees V-agrees
    (↠-step (pure-step (seal-unseal vu)) tail) vV
    (unseal-positive-not-timed
      {W = W} {θ = θ} {X = X} {A = A} {V = V} {n = zero})

complete-coerce-after-root {W = world next cells} {θ = θ}
    solver world-agreement W⊢ runtime runtime-env
    (C.cast-inst {A = body-A} {B = result-B} hB occurs c⊢)
    V⊢ θ-agrees V-agrees
    (pure-step (β-inst vu))
    tail vV tail-smaller
    with nu-value-tail (value-trace-value V-agrees)
      (value-trace-no-bullet V-agrees) tail vV
complete-coerce-after-root {W = world next cells} {θ = θ}
    solver world-agreement W⊢ runtime runtime-env
    (C.cast-inst {A = body-A} {B = result-B} hB occurs c⊢)
    V⊢ θ-agrees V-agrees
    (pure-step (β-inst vu))
    tail vV tail-smaller
    | rest-changes , refl , rest
    with decompose-cast-value-trace rest vV
complete-coerce-after-root {W = world next cells} {θ = θ}
    solver world-agreement W⊢ runtime runtime-env
    (C.cast-inst {A = body-A} {B = result-B} hB occurs c⊢)
    V⊢ θ-agrees V-agrees
    (pure-step (β-inst vu))
    tail vV tail-smaller
    | rest-changes , refl , rest
    | cast-trace-decomposition changes-I changes-C u₁ vu₁
        I-trace C-trace refl
    with solver I-smaller
      (instantiate-problem refl agreement-B W⁺⊢ allocated-here V⁺⊢
        newest V-after-bind I-trace vu₁)
  where
  path-B = allocation-path {A = ★} world-agreement θ-agrees
  agreement-B = world-trace-agreement-++ world-agreement path-B
  W⁺⊢ = allocate-world-typed W⊢ runtime wf★
  W≤W⁺ = world-extension-allocate world-extension-refl
  V⁺⊢ = value-weaken W≤W⁺ W⁺⊢ V⊢
  newest = new-seal-lookup []
    {next = next} {cells = cells} {A = ★} {θ = θ}
  V-after-bind = value-trace-path-empty
    world-agreement path-B V-agrees
  I-smaller : length changes-I < _
  I-smaller = ≤-<-trans
    (≤-trans (prefix-length≤ changes-I changes-C)
      (n≤1+n (length (changes-I ++ changes-C)))) tail-smaller
complete-coerce-after-root {W = world next cells} {θ = θ}
    solver world-agreement W⊢ runtime runtime-env
    (C.cast-inst {A = body-A} {B = result-B} hB occurs c⊢)
    V⊢ θ-agrees V-agrees
    (pure-step (β-inst vu))
    tail vV tail-smaller
    | rest-changes , refl , rest
    | cast-trace-decomposition changes-I changes-C u₁ vu₁
        I-trace C-trace refl
    | nI , W₁ , U , I-eq
    with align-instantiate-return {n = nI} {changes = changes-I}
      agreement-B newest V-after-bind I-trace vu₁ I-eq
  where
  path-B = allocation-path {A = ★} world-agreement θ-agrees
  agreement-B = world-trace-agreement-++ world-agreement path-B
  newest = new-seal-lookup []
    {next = next} {cells = cells} {A = ★} {θ = θ}
  V-after-bind = value-trace-path-empty
    world-agreement path-B V-agrees
complete-coerce-after-root {W = world next cells} {θ = θ}
    solver world-agreement W⊢ runtime runtime-env
    (C.cast-inst {A = body-A} {B = result-B} hB occurs c⊢)
    V⊢ θ-agrees V-agrees
    (pure-step (β-inst vu))
    tail vV tail-smaller
    | rest-changes , refl , rest
    | cast-trace-decomposition changes-I changes-C u₁ vu₁
        I-trace C-trace refl
    | nI , W₁ , U , I-eq | path-I , U-agrees
    with instantiate-returned-typing nI W⁺⊢ allocated-here V⁺⊢ I-eq
  where
  W⁺⊢ = allocate-world-typed W⊢ runtime wf★
  W≤W⁺ = world-extension-allocate world-extension-refl
  V⁺⊢ = value-weaken W≤W⁺ W⁺⊢ V⊢
complete-coerce-after-root {W = world next cells} {θ = θ}
    solver world-agreement W⊢ runtime runtime-env
    (C.cast-inst {A = body-A} {B = result-B} hB occurs c⊢)
    V⊢ θ-agrees V-agrees
    (pure-step (β-inst vu))
    tail vV tail-smaller
    | rest-changes , refl , rest
    | cast-trace-decomposition changes-I changes-C u₁ vu₁
        I-trace C-trace refl
    | nI , W₁ , U , I-eq | path-I , U-agrees
    | W⁺≤W₁ , W₁⊢ , U⊢
    with type-environment-trace-path agreement-B path-I
      extended-agreement
  where
  path-B = allocation-path {A = ★} world-agreement θ-agrees
  agreement-B = world-trace-agreement-++ world-agreement path-B
  outer-after-bind = type-environment-trace-bind
    {new-agreement = agreement-B} θ-agrees
  newest = new-seal-lookup []
    {next = next} {cells = cells} {A = ★} {θ = θ}
  extended-agreement =
    type-environment-instantiate-head newest outer-after-bind
complete-coerce-after-root {W = world next cells} {θ = θ} {τ = τ}
    {c = C.inst result-B c}
    solver world-agreement W⊢ runtime runtime-env
    (C.cast-inst {A = body-A} {B = result-B} hB occurs c⊢)
    V⊢ θ-agrees V-agrees
    (pure-step (β-inst vu))
    tail vV tail-smaller
    | rest-changes , refl , rest
    | cast-trace-decomposition changes-I changes-C u₁ vu₁
        I-trace C-trace refl
    | nI , W₁ , U , I-eq | path-I , U-agrees
    | W⁺≤W₁ , W₁⊢ , U⊢ | path-agreement
    with solver C-smaller
      (coerce-problem refl agreement-I W₁⊢
        (runtime-context-weaken W⁺≤W₁
          (runtime-context-seal runtime))
        (runtime-type-seal runtime-env) c⊢ U⊢′
        (type-environment-trace-rebase
          (final-agreement path-agreement)) U-agrees C-trace′ vV)
  where
  path-B = allocation-path {A = ★} world-agreement θ-agrees
  agreement-B = world-trace-agreement-++ world-agreement path-B
  agreement-I = world-trace-agreement-++ agreement-B path-I
  U⊢′ = subst (ValueTyping W₁ U)
    (instantiate-interpret
      (nominal-type (seal-name (seal-name-id next))) _ body-A) U⊢
  C-smaller : length changes-C < _
  C-smaller = ≤-<-trans
    (≤-trans (suffix-length≤ changes-I changes-C)
      (n≤1+n (length (changes-I ++ changes-C)))) tail-smaller
  final-eq = trans (coercion-action path-agreement c)
    (cong (applyCoercions changes-I)
      (renameᶜ-cong (extend-after-insertion _)
        c))
  C-trace′ = subst
    (\ d → u₁ N.⟨ d ⟩ —↠[ changes-C ] _)
    (sym final-eq) C-trace
complete-coerce-after-root {W = world next cells} {θ = θ}
    {c = C.inst result-B c} {V = V}
    solver world-agreement W⊢ runtime runtime-env
    (C.cast-inst {A = body-A} hB occurs c⊢)
    V⊢ θ-agrees V-agrees
    (pure-step (β-inst vu))
    tail vV tail-smaller
    | rest-changes , refl , rest
    | cast-trace-decomposition changes-I changes-C u₁ vu₁
        I-trace C-trace refl
    | nI , W₁ , U , I-eq | path-I , U-agrees
    | W⁺≤W₁ , W₁⊢ , U⊢ | path-agreement
    | nC , W₂ , R , C-eq =
  suc (nI + nC) , W₂ , R ,
    coerce-instantiation-from-phases
      {W = world next cells} {θ = θ} {B = result-B} {c = c}
      {V = V} {nI = nI} {W₁ = W₁} {U = U}
      {nC = nC} {W₂ = W₂} {R = R} I-eq C-eq

complete-coerce-after-root solver world-agreement W⊢ runtime runtime-env
    c⊢ V⊢ θ-agrees V-agrees
    (pure-step blame-⟨⟩) tail vV tail-smaller =
  ⊥-elim (blame-does-not-reach-value tail vV)
complete-coerce-after-root solver world-agreement W⊢ runtime runtime-env
    c⊢ V⊢ θ-agrees V-agrees
    (ξ-⟨⟩ u→u′) tail vV tail-smaller =
  ⊥-elim (value-irreducible
    (value-trace-value V-agrees) u→u′)

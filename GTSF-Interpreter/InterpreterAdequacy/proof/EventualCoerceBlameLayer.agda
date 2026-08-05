module InterpreterAdequacy.proof.EventualCoerceBlameLayer where

-- File Charter:
--   * Constructs finite blamed `coerceValue` runs from active coercion traces
--     ending in blame.
--   * Splits sequence and instantiation coercions into a successful prefix
--     followed by the unique blamed phase.
--   * Uses the return-completeness driver only for concrete value prefixes.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_; _++_; length)
open import Data.Maybe using (just)
open import Data.Nat using (_+_; _<_; _≤_; suc; zero)
open import Data.Nat.Properties using
  (<-trans; n<1+n; n≤1+n; ≤-<-trans; ≤-trans)
open import Data.Product using (_,_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)

import Coercions as C
open import Interpreter
open import InterpreterAdequacy.TraceAgreement
open import InterpreterAdequacy.proof.AllocationTrace using
  (allocation-path)
open import InterpreterAdequacy.proof.CastBlameTraceDecomposition
open import InterpreterAdequacy.proof.CastTraceDecomposition
open import InterpreterAdequacy.proof.EventualBlameProblem
open import InterpreterAdequacy.proof.EventualReturnAlignment using
  (align-coerce-return; align-instantiate-return)
import InterpreterAdequacy.proof.EventualReturnProblem as Return
open import InterpreterAdequacy.proof.EventualReturnDriver using
  (eventual-return)
open import InterpreterAdequacy.proof.EventualReturnTyping using
  (coerce-returned-typing; instantiate-returned-typing)
open import InterpreterAdequacy.proof.FiniteRunComposition using
  ( coerce-instantiation-from-coercion-blame
  ; coerce-instantiation-from-instantiation-blame
  ; coerce-sequence-from-first-blame
  ; coerce-sequence-from-second-blame
  )
open import
  InterpreterAdequacy.proof.ImmediateCoercionBlameCompleteness using
  (complete-immediate-coercion-blame)
open import InterpreterAdequacy.proof.ImmediateCoercionTermination using
  (untag-positive-not-timed)
open import InterpreterAdequacy.proof.NuBlameTraceDecomposition using
  (nu-blame-tail)
open import InterpreterAdequacy.proof.TraceAgreementBind using
  (new-seal-lookup; type-environment-trace-bind)
open import InterpreterAdequacy.proof.TraceAgreementPath using
  (type-environment-trace-rebase; value-trace-path-empty)
open import InterpreterAdequacy.proof.TraceAgreementProperties using
  (value-trace-no-bullet; value-trace-value; world-trace-agreement-++)
open import InterpreterAdequacy.proof.TraceMeasure using
  ( prefix-before-step-shorter
  ; prefix-length≤
  ; residual-after-step-shorter
  ; suffix-length≤
  )
open import InterpreterAdequacy.proof.TypeAbstractionBetaReification using
  (extend-after-insertion)
open import InterpreterAdequacy.proof.TypeAbstractionInstantiationSoundness
  using (type-environment-instantiate-head)
open import InterpreterAdequacy.proof.TypeEnvironmentTracePath
open import Typing.InterpreterSemanticTypingCore
open import NuReduction
import NuTerms as N
open import proof.Core.Properties.CoercionProperties using
  (renameᶜ-cong)
open import proof.Core.Properties.ReductionProperties using
  (applyCoercions)
open import proof.DGG.Core.NuReductionDeterminism using
  (source-blame-excludes-value; value-irreducible)
open import proof.InterpreterSemanticTypingProperties using
  ( allocated-here
  ; instantiate-interpret
  ; runtime-context-seal
  ; runtime-context-weaken
  ; value-weaken
  )
open import Types using (★; wf★)

blame-not-value : N.Value N.blame → ⊥
blame-not-value ()

complete-coerce-blame-after-root :
  ∀ {measure W prefix Δ Σ θ τ c V u A B μ} →
  StrictlySmallerBlameSolver measure →
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
  next —↠[ tail ] N.blame →
  length tail < measure →
  Σ[ n ∈ StepIndex ]
  Σ[ Z ∈ World ] coerceValue W θ c V n ≡ blamed Z

complete-coerce-blame-after-root solver world-agreement W⊢ runtime
    runtime-env (C.cast-id hA allowed) V⊢ θ-agrees V-agrees
    (pure-step (β-id vu)) tail tail-smaller =
  ⊥-elim
    (source-blame-excludes-value tail ↠-refl
      (value-trace-value V-agrees))

complete-coerce-blame-after-root {measure = measure}
    {W = W} {θ = θ} {c = c C.︔ d} {V = V} {u = u}
    solver world-agreement W⊢ runtime runtime-env
    (C.cast-seq c⊢ d⊢) V⊢ θ-agrees V-agrees
    (pure-step (β-seq vu)) tail tail-smaller
    with decompose-cast-blame-trace tail
complete-coerce-blame-after-root {measure = measure}
    {W = W} {θ = θ} {c = c C.︔ d} {V = V}
    solver world-agreement W⊢ runtime runtime-env
    (C.cast-seq c⊢ d⊢) V⊢ θ-agrees V-agrees
    (pure-step (β-seq vu)) tail tail-smaller
    | operand-blames {changes-M = changes-C} C-trace refl
    with solver C-smaller
      (coerce-problem refl world-agreement W⊢ runtime runtime-env
        c⊢ V⊢ θ-agrees V-agrees C-trace)
  where
  C-smaller : length changes-C < measure
  C-smaller = <-trans
    (prefix-before-step-shorter changes-C [] keep) tail-smaller
complete-coerce-blame-after-root {W = W} {θ = θ}
    {c = c C.︔ d} {V = V}
    solver world-agreement W⊢ runtime runtime-env
    (C.cast-seq c⊢ d⊢) V⊢ θ-agrees V-agrees
    (pure-step (β-seq vu)) tail tail-smaller
    | operand-blames C-trace refl | nC , Z , C-eq =
  suc nC , Z , coerce-sequence-from-first-blame
    {W = W} {θ = θ} {c = c} {d = d} {V = V}
    {n = nC} {Z = Z} C-eq
complete-coerce-blame-after-root {measure = measure}
    {W = W} {θ = θ} {c = c C.︔ d} {V = V}
    solver world-agreement W⊢ runtime runtime-env
    (C.cast-seq c⊢ d⊢) V⊢ θ-agrees V-agrees
    (pure-step (β-seq vu)) tail tail-smaller
    | active-blames {changes-M = changes-C}
        {changes-C = changes-D} {u = z} vz C-trace D-trace refl
    with eventual-return
      (Return.coerce-problem refl world-agreement W⊢ runtime runtime-env
        c⊢ V⊢ θ-agrees V-agrees C-trace vz)
complete-coerce-blame-after-root {measure = measure}
    {W = W} {θ = θ} {c = c C.︔ d} {V = V}
    solver world-agreement W⊢ runtime runtime-env
    (C.cast-seq c⊢ d⊢) V⊢ θ-agrees V-agrees
    (pure-step (β-seq vu)) tail tail-smaller
    | active-blames {changes-M = changes-C}
        {changes-C = changes-D} {u = z} vz C-trace D-trace refl
    | nC , W₁ , U , C-eq
    with align-coerce-return {n = nC} {changes = changes-C}
      world-agreement θ-agrees V-agrees C-trace vz C-eq
complete-coerce-blame-after-root {measure = measure}
    {W = W} {θ = θ} {c = c C.︔ d} {V = V}
    solver world-agreement W⊢ runtime runtime-env
    (C.cast-seq c⊢ d⊢) V⊢ θ-agrees V-agrees
    (pure-step (β-seq vu)) tail tail-smaller
    | active-blames {changes-M = changes-C}
        {changes-C = changes-D} {u = z} vz C-trace D-trace refl
    | nC , W₁ , U , C-eq | path-C , U-agrees
    with coerce-returned-typing nC W⊢ runtime runtime-env c⊢ V⊢ C-eq
complete-coerce-blame-after-root {measure = measure}
    {W = W} {θ = θ} {c = c C.︔ d} {V = V}
    solver world-agreement W⊢ runtime runtime-env
    (C.cast-seq c⊢ d⊢) V⊢ θ-agrees V-agrees
    (pure-step (β-seq vu)) tail tail-smaller
    | active-blames {changes-M = changes-C}
        {changes-C = changes-D} {u = z} vz C-trace D-trace refl
    | nC , W₁ , U , C-eq | path-C , U-agrees
    | W≤W₁ , W₁⊢ , U⊢
    with type-environment-trace-path world-agreement path-C θ-agrees
complete-coerce-blame-after-root {measure = measure}
    {W = W} {θ = θ} {c = c C.︔ d} {V = V}
    solver world-agreement W⊢ runtime runtime-env
    (C.cast-seq c⊢ d⊢) V⊢ θ-agrees V-agrees
    (pure-step (β-seq vu)) tail tail-smaller
    | active-blames {changes-M = changes-C}
        {changes-C = changes-D} {u = z} vz C-trace D-trace refl
    | nC , W₁ , U , C-eq | path-C , U-agrees
    | W≤W₁ , W₁⊢ , U⊢ | path-agreement
    with solver D-smaller
      (coerce-problem refl agreement-C W₁⊢
        (runtime-context-weaken W≤W₁ runtime) runtime-env d⊢ U⊢
        (type-environment-trace-rebase
          (final-agreement path-agreement)) U-agrees D-trace′)
  where
  agreement-C = world-trace-agreement-++ world-agreement path-C
  D-smaller : length changes-D < measure
  D-smaller = ≤-<-trans
    (suffix-length≤ changes-C changes-D) tail-smaller
  D-trace′ = subst
    (λ d′ → z N.⟨ d′ ⟩ —↠[ _ ] N.blame)
    (sym (coercion-action path-agreement d)) D-trace
complete-coerce-blame-after-root {W = W} {θ = θ}
    {c = c C.︔ d} {V = V}
    solver world-agreement W⊢ runtime runtime-env
    (C.cast-seq c⊢ d⊢) V⊢ θ-agrees V-agrees
    (pure-step (β-seq vu)) tail tail-smaller
    | active-blames {changes-M = changes-C}
        {changes-C = changes-D} {u = z} vz C-trace D-trace refl
    | nC , W₁ , U , C-eq | path-C , U-agrees
    | W≤W₁ , W₁⊢ , U⊢ | path-agreement
    | nD , Z , D-eq =
  suc (nC + nD) , Z , coerce-sequence-from-second-blame
    {W = W} {θ = θ} {c = c} {d = d} {V = V}
    {nC = nC} {W₁ = W₁} {U = U} {nD = nD} C-eq D-eq

complete-coerce-blame-after-root {W = W} {θ = θ}
    {c = H C.？} {V = V}
    solver world-agreement W⊢ runtime runtime-env
    c⊢@(C.cast-untag hG gG allowed) V⊢ θ-agrees V-agrees
    (pure-step (tag-untag-ok vu)) tail tail-smaller =
  ⊥-elim (source-blame-excludes-value tail ↠-refl vu)
complete-coerce-blame-after-root {W = W} {θ = θ}
    {c = H C.？} {V = V}
    solver world-agreement W⊢ runtime runtime-env
    c⊢@(C.cast-untag hG gG allowed) V⊢ θ-agrees V-agrees
    (pure-step (tag-untag-bad vu G≢H)) tail tail-smaller
    with complete-immediate-coercion-blame
      world-agreement W⊢ runtime runtime-env c⊢ V⊢ θ-agrees V-agrees
      (↠-step (pure-step (tag-untag-bad vu G≢H)) tail)
      (untag-positive-not-timed
        {W = W} {θ = θ} {G = H} {V = V} {n = zero})
complete-coerce-blame-after-root solver world-agreement W⊢ runtime
    runtime-env c⊢ V⊢ θ-agrees V-agrees
    (pure-step (tag-untag-bad vu G≢H)) tail tail-smaller
    | Z , result-eq =
  suc zero , Z , result-eq

complete-coerce-blame-after-root solver world-agreement W⊢ runtime
    runtime-env (C.cast-unseal hA X∈ allowed) V⊢ θ-agrees V-agrees
    (pure-step (seal-unseal vu)) tail tail-smaller =
  ⊥-elim (source-blame-excludes-value tail ↠-refl vu)

complete-coerce-blame-after-root {measure = measure}
    {W = world next cells} {θ = θ} {τ = τ}
    {c = C.inst result-B c} {V = V}
    solver world-agreement W⊢ runtime runtime-env
    (C.cast-inst {A = body-A} hB occurs c⊢)
    V⊢ θ-agrees V-agrees (pure-step (β-inst vu)) tail tail-smaller
    with nu-blame-tail (value-trace-value V-agrees)
      (value-trace-no-bullet V-agrees) tail
complete-coerce-blame-after-root {measure = measure}
    {W = world next cells} {θ = θ} {τ = τ}
    {c = C.inst result-B c} {V = V}
    solver world-agreement W⊢ runtime runtime-env
    (C.cast-inst {A = body-A} hB occurs c⊢)
    V⊢ θ-agrees V-agrees (pure-step (β-inst vu)) tail tail-smaller
    | rest-changes , refl , rest
    with decompose-cast-blame-trace rest
complete-coerce-blame-after-root {measure = measure}
    {W = world next cells} {θ = θ} {τ = τ}
    {c = C.inst result-B c} {V = V}
    solver world-agreement W⊢ runtime runtime-env
    (C.cast-inst {A = body-A} hB occurs c⊢)
    V⊢ θ-agrees V-agrees (pure-step (β-inst vu)) tail tail-smaller
    | .(changes-I ++ (keep ∷ [])) , refl , rest
    | operand-blames {changes-M = changes-I} I-trace refl
    with solver I-smaller
      (instantiate-problem refl agreement-B W⁺⊢ allocated-here V⁺⊢
        newest V-after-bind I-trace)
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
  I-smaller : length changes-I < measure
  I-smaller = <-trans
    (<-trans (prefix-before-step-shorter changes-I [] keep)
      (n<1+n (length (changes-I ++ (keep ∷ []))))) tail-smaller
complete-coerce-blame-after-root {W = world next cells} {θ = θ}
    {c = C.inst result-B c} {V = V}
    solver world-agreement W⊢ runtime runtime-env
    (C.cast-inst {A = body-A} hB occurs c⊢)
    V⊢ θ-agrees V-agrees (pure-step (β-inst vu)) tail tail-smaller
    | .(_ ++ (keep ∷ [])) , refl , rest
    | operand-blames I-trace refl | nI , Z , I-eq =
  suc nI , Z , coerce-instantiation-from-instantiation-blame
    {W = world next cells} {θ = θ} {B = result-B} {c = c}
    {V = V} {nI = nI} I-eq
complete-coerce-blame-after-root {measure = measure}
    {W = world next cells} {θ = θ} {τ = τ}
    {c = C.inst result-B c} {V = V}
    solver world-agreement W⊢ runtime runtime-env
    (C.cast-inst {A = body-A} hB occurs c⊢)
    V⊢ θ-agrees V-agrees (pure-step (β-inst vu)) tail tail-smaller
    | .(changes-I ++ changes-C) , refl , rest
    | active-blames {changes-I} {changes-C} {u₁}
        vu₁ I-trace C-trace refl
    with eventual-return
      (Return.instantiate-problem refl agreement-B W⁺⊢ allocated-here
        V⁺⊢ newest V-after-bind I-trace vu₁)
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
complete-coerce-blame-after-root {measure = measure}
    {W = world next cells} {θ = θ} {τ = τ}
    {c = C.inst result-B c} {V = V}
    solver world-agreement W⊢ runtime runtime-env
    (C.cast-inst {A = body-A} hB occurs c⊢)
    V⊢ θ-agrees V-agrees (pure-step (β-inst vu)) tail tail-smaller
    | .(changes-I ++ changes-C) , refl , rest
    | active-blames {changes-I} {changes-C} {u₁}
        vu₁ I-trace C-trace refl
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
complete-coerce-blame-after-root {measure = measure}
    {W = world next cells} {θ = θ} {τ = τ}
    {c = C.inst result-B c} {V = V}
    solver world-agreement W⊢ runtime runtime-env
    (C.cast-inst {A = body-A} hB occurs c⊢)
    V⊢ θ-agrees V-agrees (pure-step (β-inst vu)) tail tail-smaller
    | .(changes-I ++ changes-C) , refl , rest
    | active-blames {changes-I} {changes-C} {u₁}
        vu₁ I-trace C-trace refl
    | nI , W₁ , U , I-eq | path-I , U-agrees
    with instantiate-returned-typing nI W⁺⊢ allocated-here V⁺⊢ I-eq
  where
  W⁺⊢ = allocate-world-typed W⊢ runtime wf★
  W≤W⁺ = world-extension-allocate world-extension-refl
  V⁺⊢ = value-weaken W≤W⁺ W⁺⊢ V⊢
complete-coerce-blame-after-root {measure = measure}
    {W = world next cells} {θ = θ} {τ = τ}
    {c = C.inst result-B c} {V = V}
    solver world-agreement W⊢ runtime runtime-env
    (C.cast-inst {A = body-A} hB occurs c⊢)
    V⊢ θ-agrees V-agrees (pure-step (β-inst vu)) tail tail-smaller
    | .(changes-I ++ changes-C) , refl , rest
    | active-blames {changes-I} {changes-C} {u₁}
        vu₁ I-trace C-trace refl
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
complete-coerce-blame-after-root {measure = measure}
    {W = world next cells} {θ = θ} {τ = τ}
    {c = C.inst result-B c} {V = V}
    solver world-agreement W⊢ runtime runtime-env
    (C.cast-inst {A = body-A} hB occurs c⊢)
    V⊢ θ-agrees V-agrees (pure-step (β-inst vu)) tail tail-smaller
    | .(changes-I ++ changes-C) , refl , rest
    | active-blames {changes-I} {changes-C} {u₁}
        vu₁ I-trace C-trace refl
    | nI , W₁ , U , I-eq | path-I , U-agrees
    | W⁺≤W₁ , W₁⊢ , U⊢ | path-agreement
    with solver C-smaller
      (coerce-problem refl agreement-I W₁⊢
        (runtime-context-weaken W⁺≤W₁
          (runtime-context-seal runtime))
        (runtime-type-seal runtime-env) c⊢ U⊢′
        (type-environment-trace-rebase
          (final-agreement path-agreement)) U-agrees C-trace′)
  where
  path-B = allocation-path {A = ★} world-agreement θ-agrees
  agreement-B = world-trace-agreement-++ world-agreement path-B
  agreement-I = world-trace-agreement-++ agreement-B path-I
  U⊢′ = subst (ValueTyping W₁ U)
    (instantiate-interpret
      (nominal-type (seal-name (seal-name-id next))) _ body-A) U⊢
  C-smaller : length changes-C < measure
  C-smaller = ≤-<-trans
    (≤-trans (suffix-length≤ changes-I changes-C)
      (n≤1+n (length (changes-I ++ changes-C)))) tail-smaller
  final-eq = trans (coercion-action path-agreement c)
    (cong (applyCoercions changes-I)
      (renameᶜ-cong (extend-after-insertion _) c))
  C-trace′ = subst
    (λ d → u₁ N.⟨ d ⟩ —↠[ changes-C ] N.blame)
    (sym final-eq) C-trace
complete-coerce-blame-after-root {W = world next cells} {θ = θ}
    {c = C.inst result-B c} {V = V}
    solver world-agreement W⊢ runtime runtime-env
    (C.cast-inst {A = body-A} hB occurs c⊢)
    V⊢ θ-agrees V-agrees (pure-step (β-inst vu)) tail tail-smaller
    | .(changes-I ++ changes-C) , refl , rest
    | active-blames {changes-I} {changes-C} {u₁}
        vu₁ I-trace C-trace refl
    | nI , W₁ , U , I-eq | path-I , U-agrees
    | W⁺≤W₁ , W₁⊢ , U⊢ | path-agreement
    | nC , Z , C-eq =
  suc (nI + nC) , Z , coerce-instantiation-from-coercion-blame
    {W = world next cells} {θ = θ} {B = result-B} {c = c}
    {V = V} {nI = nI} {W₁ = W₁} {U = U} {nC = nC}
    I-eq C-eq

complete-coerce-blame-after-root solver world-agreement W⊢ runtime
    runtime-env c⊢ V⊢ θ-agrees V-agrees
    (pure-step blame-⟨⟩) tail tail-smaller =
  ⊥-elim (blame-not-value (value-trace-value V-agrees))
complete-coerce-blame-after-root solver world-agreement W⊢ runtime
    runtime-env c⊢ V⊢ θ-agrees V-agrees
    (ξ-⟨⟩ u→u′) tail tail-smaller =
  ⊥-elim (value-irreducible (value-trace-value V-agrees) u→u′)

module InterpreterAdequacy.proof.EventualInterpretNu where

-- File Charter:
--   * Constructs a finite interpreter return for a terminating source `ν`
--     by synchronizing operand evaluation, allocation, bullet instantiation,
--     and the residual coercion.
--   * Transports the lexical type and coercion across the concrete operand
--     trace before matching the interpreter's fresh allocation.
--   * Receives recursive completeness only through `StrictlySmallerSolver`.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_; _++_; length)
open import Data.Maybe using (just)
open import Data.Nat using (_+_; _<_; _≤_; suc; zero)
open import Data.Nat.Properties using (≤-<-trans)
open import Data.Product using (_,_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)

import Coercions as C
open import Interpreter
open import InterpreterAdequacy.TraceAgreement
open import InterpreterAdequacy.proof.AllocationTrace using
  (allocation-path)
open import InterpreterAdequacy.proof.CastTraceDecomposition
open import InterpreterAdequacy.proof.EventualReturnAlignment using
  (align-coerce-return; align-instantiate-return; align-interpret-return)
open import InterpreterAdequacy.proof.EventualReturnProblem
open import InterpreterAdequacy.proof.EventualReturnTyping using
  (coerce-returned-typing; instantiate-returned-typing;
   interpret-returned-typing)
open import InterpreterAdequacy.proof.FiniteRunComposition using
  (interpret-nu-from-phases)
open import InterpreterAdequacy.proof.NuTraceDecomposition
open import InterpreterAdequacy.proof.TraceAgreementBind using
  (newest-allocation-lookup; type-environment-trace-bind)
open import InterpreterAdequacy.proof.TraceAgreementPath using
  (term-trace-path-empty; type-environment-trace-rebase;
   value-trace-path-empty)
open import InterpreterAdequacy.proof.TraceAgreementProperties using
  (world-trace-agreement-++)
open import InterpreterAdequacy.proof.TraceMeasure using
  (prefix-before-step-shorter; prefix-length≤;
   residual-after-step-shorter; suffix-length≤)
open import InterpreterAdequacy.proof.TypeAbstractionBetaReification using
  (extend-after-insertion)
open import InterpreterAdequacy.proof.TypeAbstractionInstantiationSoundness
  using (type-environment-instantiate-head)
open import InterpreterAdequacy.proof.TypeEnvironmentTracePath
open import Typing.InterpreterSemanticTypingCore
open import SmallStepInterface.InterpreterTermShape using (InterpreterTerm)
open import NuReduction
import NuTerms as N
open import proof.Core.Properties.CoercionProperties using
  (renameᶜ-cong)
open import proof.Core.Properties.ReductionProperties using
  (applyCoercions)
open import proof.InterpreterSemanticTypingProperties using
  ( allocated-here
  ; environment-weaken
  ; instantiate-interpret
  ; runtime-context-seal
  ; runtime-context-weaken
  ; value-weaken
  )
open import InterpreterAdequacy.proof.InterpreterTermNoBullet using
  (interpreter-term-no-bullet)
import Types

complete-interpret-nu :
  ∀ {measure W prefix Δ Σ Γ γ θ A L c P B changes v} →
  StrictlySmallerSolver measure →
  length changes ≡ measure →
  (world-agreement : WorldTraceAgreement W prefix) →
  (W⊢ : WorldTyping W) →
  (runtime : RuntimeContext W Δ Σ θ) →
  (runtime-env : RuntimeTypeEnvironment θ) →
  (environment : EnvironmentTyping W θ γ Γ) →
  (L-image : InterpreterTerm L) →
  N._∣_∣_⊢_⦂_ Δ Σ Γ (N.ν A L c) B →
  TermTraceAgreement world-agreement [] γ θ (N.ν A L c) P →
  P —↠[ changes ] v →
  N.Value v →
  Σ[ n ∈ StepIndex ]
  Σ[ Z ∈ World ]
  Σ[ R ∈ Value ] interpret W γ θ (N.ν A L c) n ≡ returned Z R
complete-interpret-nu solver measure-eq world-agreement W⊢ runtime
    runtime-env environment L-image (N.⊢ν hA L⊢ c⊢)
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace vV
    with decompose-nu-value-trace trace′ vV
  where
  trace′ = subst (\ Q → Q —↠[ _ ] _)
    reification trace
complete-interpret-nu solver measure-eq world-agreement W⊢ runtime
    runtime-env environment L-image (N.⊢ν hA L⊢ c⊢)
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace vV
    | nu-trace-decomposition changes-L active-changes
        f vf no-f L-trace active refl
    with nu-value-tail vf no-f active vV
complete-interpret-nu solver measure-eq world-agreement W⊢ runtime
    runtime-env environment L-image (N.⊢ν hA L⊢ c⊢)
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace vV
    | nu-trace-decomposition changes-L (bind A-active ∷ rest-changes)
        f vf no-f L-trace active refl
    | rest-changes , refl , rest
    with decompose-cast-value-trace rest vV
complete-interpret-nu solver measure-eq world-agreement W⊢ runtime
    runtime-env environment L-image (N.⊢ν hA L⊢ c⊢)
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace vV
    | nu-trace-decomposition changes-L
        (bind A-active ∷ .(changes-I ++ changes-C))
        f vf no-f L-trace active refl
    | .(changes-I ++ changes-C) , refl , rest
    | cast-trace-decomposition changes-I changes-C u vu
        I-trace C-trace refl
    with solver L-smaller
      (interpret-problem refl world-agreement W⊢ runtime runtime-env
        environment L-image L⊢ L-agrees L-trace vf)
  where
  L-agrees = term-trace-agreement τ vs θ-agrees γ-agrees refl
  L-smaller : length changes-L < _
  L-smaller = subst (length changes-L <_) measure-eq
    (prefix-before-step-shorter changes-L (changes-I ++ changes-C)
      (bind A-active))
complete-interpret-nu solver measure-eq world-agreement W⊢ runtime
    runtime-env environment L-image (N.⊢ν hA L⊢ c⊢)
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace vV
    | nu-trace-decomposition changes-L
        (bind A-active ∷ .(changes-I ++ changes-C))
        f vf no-f L-trace active refl
    | .(changes-I ++ changes-C) , refl , rest
    | cast-trace-decomposition changes-I changes-C u vu
        I-trace C-trace refl
    | nL , W₁ , F , L-eq
    with align-interpret-return {n = nL} {changes = changes-L}
      world-agreement (interpreter-term-no-bullet L-image) L-agrees
      L-trace vf L-eq
  where
  L-agrees = term-trace-agreement τ vs θ-agrees γ-agrees refl
complete-interpret-nu solver measure-eq world-agreement W⊢ runtime
    runtime-env environment L-image (N.⊢ν hA L⊢ c⊢)
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace vV
    | nu-trace-decomposition changes-L
        (bind A-active ∷ .(changes-I ++ changes-C))
        f vf no-f L-trace active refl
    | .(changes-I ++ changes-C) , refl , rest
    | cast-trace-decomposition changes-I changes-C u vu
        I-trace C-trace refl
    | nL , W₁ , F , L-eq | path-L , F-agrees
    with interpret-returned-typing nL W⊢ runtime runtime-env
      environment L-image L⊢ L-eq
complete-interpret-nu {A = A}
    solver measure-eq world-agreement W⊢ runtime
    runtime-env environment L-image (N.⊢ν {C = body-C} hA L⊢ c⊢)
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace vV
    | nu-trace-decomposition changes-L
        (bind A-active ∷ .(changes-I ++ changes-C))
        f vf no-f L-trace active refl
    | .(changes-I ++ changes-C) , refl , rest
    | cast-trace-decomposition changes-I changes-C u vu
        I-trace C-trace refl
    | nL , W₁ , F , L-eq | path-L , F-agrees
    | W≤W₁ , W₁⊢ , F⊢
    with type-environment-trace-path world-agreement path-L θ-agrees
complete-interpret-nu {W = W} {θ = θ} {A = A}
    solver measure-eq world-agreement W⊢ runtime
    runtime-env environment L-image
      (N.⊢ν {C = body-C} hA L⊢ c⊢)
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace vV
    | nu-trace-decomposition changes-L
        (bind A-active ∷ .(changes-I ++ changes-C))
        f vf no-f L-trace active refl
    | .(changes-I ++ changes-C) , refl , rest
    | cast-trace-decomposition changes-I changes-C u vu
        I-trace C-trace refl
    | nL , W₁ , F , L-eq | path-L , F-agrees
    | W≤W₁ , W₁⊢ , F⊢ | path-agreement-L
    with solver I-smaller
      (instantiate-problem {α = freshSealName W₁} refl agreement-B
        W⁺⊢ allocated-here F⁺⊢ newest F-after-bind I-trace vu)
  where
  agreement-L = world-trace-agreement-++ world-agreement path-L
  canonical-bind = allocation-path {A = A} agreement-L
    (final-agreement path-agreement-L)
  path-B = subst
    (\ B₁ → WorldTracePath W₁ (bind B₁ ∷ []) (allocate W₁ A θ))
    (type-action path-agreement-L A) canonical-bind
  agreement-B = world-trace-agreement-++ agreement-L path-B
  runtime-L = runtime-context-weaken W≤W₁ runtime
  W⁺⊢ = allocate-world-typed W₁⊢ runtime-L hA
  W₁≤W⁺ = world-extension-allocate world-extension-refl
  F⁺⊢ = value-weaken W₁≤W⁺ W⁺⊢ F⊢
  newest :
    lookup (visibleTypeNames [] (allocate W₁ A θ)) zero ≡
      just (seal-name (freshSealName W₁))
  newest = newest-allocation-lookup {W = W₁} {A = A} {θ = θ}
  F-after-bind = value-trace-path-empty agreement-L path-B F-agrees
  I-smaller : length changes-I < _
  I-smaller = subst (length changes-I <_) measure-eq
    (≤-<-trans (prefix-length≤ changes-I changes-C)
      (residual-after-step-shorter changes-L
        (changes-I ++ changes-C) (bind A-active)))
complete-interpret-nu {θ = θ} {A = A}
    solver measure-eq world-agreement W⊢ runtime
    runtime-env environment L-image
      (N.⊢ν {C = body-C} hA L⊢ c⊢)
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace vV
    | nu-trace-decomposition changes-L
        (bind A-active ∷ .(changes-I ++ changes-C))
        f vf no-f L-trace active refl
    | .(changes-I ++ changes-C) , refl , rest
    | cast-trace-decomposition changes-I changes-C u vu
        I-trace C-trace refl
    | nL , W₁ , F , L-eq | path-L , F-agrees
    | W≤W₁ , W₁⊢ , F⊢ | path-agreement-L
    | nI , W₂ , U , I-eq
    with align-instantiate-return {n = nI} {changes = changes-I}
      agreement-B newest F-after-bind I-trace vu I-eq
  where
  agreement-L = world-trace-agreement-++ world-agreement path-L
  canonical-bind = allocation-path {A = A} agreement-L
    (final-agreement path-agreement-L)
  path-B = subst
    (\ B₁ → WorldTracePath W₁ (bind B₁ ∷ []) (allocate W₁ A θ))
    (type-action path-agreement-L A) canonical-bind
  agreement-B = world-trace-agreement-++ agreement-L path-B
  newest :
    lookup (visibleTypeNames [] (allocate W₁ A θ)) zero ≡
      just (seal-name (freshSealName W₁))
  newest = newest-allocation-lookup {W = W₁} {A = A} {θ = θ}
  F-after-bind = value-trace-path-empty agreement-L path-B F-agrees
complete-interpret-nu {A = A}
    solver measure-eq world-agreement W⊢ runtime
    runtime-env environment L-image
      (N.⊢ν {C = body-C} hA L⊢ c⊢)
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace vV
    | nu-trace-decomposition changes-L
        (bind A-active ∷ .(changes-I ++ changes-C))
        f vf no-f L-trace active refl
    | .(changes-I ++ changes-C) , refl , rest
    | cast-trace-decomposition changes-I changes-C u vu
        I-trace C-trace refl
    | nL , W₁ , F , L-eq | path-L , F-agrees
    | W≤W₁ , W₁⊢ , F⊢ | path-agreement-L
    | nI , W₂ , U , I-eq | path-I , U-agrees
    with instantiate-returned-typing nI W⁺⊢ allocated-here F⁺⊢ I-eq
  where
  runtime-L = runtime-context-weaken W≤W₁ runtime
  W⁺⊢ = allocate-world-typed W₁⊢ runtime-L hA
  W₁≤W⁺ = world-extension-allocate world-extension-refl
  F⁺⊢ = value-weaken W₁≤W⁺ W⁺⊢ F⊢
complete-interpret-nu {W = W} {θ = θ} {A = A} {c = c}
    solver measure-eq world-agreement W⊢ runtime
    runtime-env environment L-image
      (N.⊢ν {C = body-C} hA L⊢ c⊢)
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace vV
    | nu-trace-decomposition changes-L
        (bind A-active ∷ .(changes-I ++ changes-C))
        f vf no-f L-trace active refl
    | .(changes-I ++ changes-C) , refl , rest
    | cast-trace-decomposition changes-I changes-C u vu
        I-trace C-trace refl
    | nL , W₁ , F , L-eq | path-L , F-agrees
    | W≤W₁ , W₁⊢ , F⊢ | path-agreement-L
    | nI , W₂ , U , I-eq | path-I , U-agrees
    | W⁺≤W₂ , W₂⊢ , U⊢
    with type-environment-trace-path agreement-B path-I
      extended-agreement
  where
  agreement-L = world-trace-agreement-++ world-agreement path-L
  canonical-bind = allocation-path {A = A} agreement-L
    (final-agreement path-agreement-L)
  path-B = subst
    (\ B₁ → WorldTracePath W₁ (bind B₁ ∷ []) (allocate W₁ A θ))
    (type-action path-agreement-L A) canonical-bind
  agreement-B = world-trace-agreement-++ agreement-L path-B
  outer-after-bind = type-environment-trace-bind
    {new-agreement = agreement-B} (final-agreement path-agreement-L)
  newest :
    lookup (visibleTypeNames [] (allocate W₁ A θ)) zero ≡
      just (seal-name (freshSealName W₁))
  newest = newest-allocation-lookup {W = W₁} {A = A} {θ = θ}
  extended-agreement =
    type-environment-instantiate-head {α = freshSealName W₁}
      newest outer-after-bind
complete-interpret-nu {W = W} {θ = θ} {A = A} {c = c}
    solver measure-eq world-agreement W⊢ runtime
    runtime-env environment L-image
      (N.⊢ν {C = body-C} hA L⊢ c⊢)
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace vV
    | nu-trace-decomposition changes-L
        (bind A-active ∷ .(changes-I ++ changes-C))
        f vf no-f L-trace active refl
    | .(changes-I ++ changes-C) , refl , rest
    | cast-trace-decomposition changes-I changes-C u vu
        I-trace C-trace refl
    | nL , W₁ , F , L-eq | path-L , F-agrees
    | W≤W₁ , W₁⊢ , F⊢ | path-agreement-L
    | nI , W₂ , U , I-eq | path-I , U-agrees
    | W⁺≤W₂ , W₂⊢ , U⊢ | path-agreement-I
    with solver C-smaller
      (coerce-problem refl agreement-I W₂⊢
        (runtime-context-weaken W⁺≤W₂
          (runtime-context-seal runtime-L))
        (runtime-type-seal runtime-env) c⊢ U⊢′
        (type-environment-trace-rebase
          (final-agreement path-agreement-I)) U-agrees C-trace′ vV)
  where
  agreement-L = world-trace-agreement-++ world-agreement path-L
  canonical-bind = allocation-path {A = A} agreement-L
    (final-agreement path-agreement-L)
  path-B = subst
    (\ B₁ → WorldTracePath W₁ (bind B₁ ∷ []) (allocate W₁ A θ))
    (type-action path-agreement-L A) canonical-bind
  agreement-B = world-trace-agreement-++ agreement-L path-B
  agreement-I = world-trace-agreement-++ agreement-B path-I
  runtime-L = runtime-context-weaken W≤W₁ runtime
  U⊢′ = subst (ValueTyping W₂ U)
    (instantiate-interpret
      (nominal-type (seal-name (freshSealName W₁))) θ body-C) U⊢
  C-smaller : length changes-C < _
  C-smaller = subst (length changes-C <_) measure-eq
    (≤-<-trans (suffix-length≤ changes-I changes-C)
      (residual-after-step-shorter changes-L
        (changes-I ++ changes-C) (bind A-active)))
  final-eq = trans (coercion-action path-agreement-I c)
    (cong (applyCoercions changes-I)
      (trans
        (renameᶜ-cong
          (extend-after-insertion (final-renaming path-agreement-L)) c)
        (binder-coercion-action path-agreement-L c)))
  C-trace′ = subst
    (\ d → u N.⟨ d ⟩ —↠[ changes-C ] _)
    (sym final-eq) C-trace
complete-interpret-nu {W = W} {γ = γ} {θ = θ}
    {A = A} {L = L} {c = c}
    solver measure-eq world-agreement W⊢ runtime
    runtime-env environment L-image (N.⊢ν hA L⊢ c⊢)
    (term-trace-agreement τ vs θ-agrees γ-agrees reification)
    trace vV
    | nu-trace-decomposition changes-L
        (bind A-active ∷ .(changes-I ++ changes-C))
        f vf no-f L-trace active refl
    | .(changes-I ++ changes-C) , refl , rest
    | cast-trace-decomposition changes-I changes-C u vu
        I-trace C-trace refl
    | nL , W₁ , F , L-eq | path-L , F-agrees
    | W≤W₁ , W₁⊢ , F⊢ | path-agreement-L
    | nI , W₂ , U , I-eq | path-I , U-agrees
    | W⁺≤W₂ , W₂⊢ , U⊢ | path-agreement-I
    | nC , W₃ , R , C-eq =
  suc (nL + (nI + nC)) , W₃ , R ,
    interpret-nu-from-phases
      {W = W} {γ = γ} {θ = θ} {A = A} {L = L} {c = c}
      {nL = nL} {W₁ = W₁} {V = F}
      {nI = nI} {W₂ = W₂} {U = U}
      {nC = nC} {W₃ = W₃} {R = R} L-eq I-eq C-eq

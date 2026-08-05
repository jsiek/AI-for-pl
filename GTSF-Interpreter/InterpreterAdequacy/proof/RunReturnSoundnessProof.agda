module InterpreterAdequacy.proof.RunReturnSoundnessProof where

-- File Charter:
--   * Proves successful direct-interpreter runs sound with respect to the
--     Nu small-step semantics by induction on interpreter fuel.
--   * Simulates `interpret`, `applyValue`, `instantiateValue`, and
--     `coerceValue` mutually, retaining exact allocation traces.
--   * Uses no progress, preservation, evaluator, or DGG result.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_; _++_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)

import Coercions as C
open import Interpreter
open import InterpreterAdequacy.TraceAgreement
open import InterpreterAdequacy.proof.AllocationTrace using
  (allocation-path)
open import InterpreterAdequacy.proof.ApplicationTraceAssembly using
  (assemble-application-return)
open import InterpreterAdequacy.proof.ClosureApplicationSoundness using
  (closure-application-from-body)
open import InterpreterAdequacy.proof.CoercionEliminationSoundness using
  (untag-return-sound; unseal-return-sound)
open import InterpreterAdequacy.proof.CoercionImmediateSoundness
open import InterpreterAdequacy.proof.InterpreterImmediateSoundness
open import InterpreterAdequacy.proof.ReturnTrace
open import InterpreterAdequacy.proof.ReturnTraceContinuation
open import InterpreterAdequacy.proof.SyntaxReification using
  (reified-term; reified-term-no-bullet)
open import InterpreterAdequacy.proof.TraceAgreementBind using
  (new-seal-lookup; type-environment-trace-bind)
open import InterpreterAdequacy.proof.TraceAgreementPath using
  (term-trace-path-empty; value-trace-path-empty; value-trace-rebase)
open import InterpreterAdequacy.proof.TraceAgreementProperties using
  ( value-trace-no-bullet
  ; value-trace-value
  ; world-trace-agreement-++
  ; world-trace-path-++
  )
open import InterpreterAdequacy.proof.TypeAbstractionBetaReification using
  (extend-after-insertion; open-extended-coercion)
open import InterpreterAdequacy.proof.TypeAbstractionInstantiationSoundness
  using
    ( type-abstraction-instantiation-return-sound
    ; type-environment-instantiate-head
    )
open import InterpreterAdequacy.proof.TypeEnvironmentTracePath
open import NuReduction using
  ( bind
  ; applyTys
  ; keep
  ; pure-step
  ; ν-step
  ; β-↦
  ; β-∀•
  ; β-gen•
  ; β-inst
  ; β-seq
  ; δ-⊕
  ; ↠-refl
  ; ↠-step
  ; _—↠[_]_
  )
import NuTerms as N
import Primitives
open import proof.Core.Properties.NuTermProperties using
  (renameᵗᵐ-preserves-No•; renameᵗᵐ-preserves-Value)
open import proof.Core.Properties.CoercionProperties using
  (renameᶜ-cong)
open import proof.Core.Properties.ReductionProperties using
  ( applyCoercions
  ; applyTerms-const
  ; applyCoercionUnderTyBinders
  ; cast-↠
  ; ν-↠
  ; ⊕₁-↠
  ; ⊕₂-↠
  ; ·₂-↠
  ; ↠-trans
  )
open import Types using (extᵗ; renameᵗ; ★)

mutual
  interpret-return-soundᵢ :
    ∀ n {W prefix γ θ M P U V}
      (world-agreement : WorldTraceAgreement W prefix) →
    N.No• M →
    TermTraceAgreement world-agreement [] γ θ M P →
    interpret W γ θ M n ≡ returned U V →
    ReturnTrace world-agreement P U V

  apply-return-soundᵢ :
    ∀ n {W prefix F f U u Z R}
      (world-agreement : WorldTraceAgreement W prefix) →
    ValueTraceAgreement world-agreement [] F f →
    ValueTraceAgreement world-agreement [] U u →
    applyValue W F U n ≡ returned Z R →
    ReturnTrace world-agreement (f N.· u) Z R

  instantiate-return-soundᵢ :
    ∀ n {W prefix α F f Z R}
      (world-agreement : WorldTraceAgreement W prefix) →
    lookup (visibleTypeNames [] W) zero ≡ just (seal-name α) →
    ValueTraceAgreement world-agreement [] F f →
    instantiateValue W α F n ≡ returned Z R →
    ReturnTrace world-agreement (f N.•) Z R

  coerce-return-soundᵢ :
    ∀ n {W prefix θ τ V v Z R}
      (world-agreement : WorldTraceAgreement W prefix) →
    TypeEnvironmentTraceAgreement world-agreement [] θ τ →
    ValueTraceAgreement world-agreement [] V v →
    ∀ {c} →
    coerceValue W θ c V n ≡ returned Z R →
    ReturnTrace world-agreement (v N.⟨ C.renameᶜ τ c ⟩) Z R

  finish-nu-returnᵢ :
    ∀ n {W prefix W₁ U R γ θ L A c τ PL F f χL}
      (world-agreement : WorldTraceAgreement W prefix) →
    TypeEnvironmentTraceAgreement world-agreement [] θ τ →
    (path-L : WorldTracePath W χL W₁) →
    ValueTraceAgreement
      (world-trace-agreement-++ world-agreement path-L) [] F f →
    PL —↠[ χL ] f →
    interpret W γ θ L n ≡ returned W₁ F →
    interpret W γ θ (N.ν A L c) (suc n) ≡ returned U R →
    ReturnTrace world-agreement
      (N.ν (renameᵗ τ A) PL (C.renameᶜ (extᵗ τ) c)) U R

  interpret-return-soundᵢ zero world-agreement no-M M-agrees ()

  interpret-return-soundᵢ (suc n) {W = W} {γ = γ} {θ = θ}
      {M = N.` x} world-agreement N.no•-`
      M-agrees result-eq
      with lookup γ x in lookup-eq
  interpret-return-soundᵢ (suc n) {M = N.` x} world-agreement N.no•-`
      M-agrees refl | just V =
    variable-return-sound M-agrees lookup-eq
  interpret-return-soundᵢ (suc n) {M = N.` x} world-agreement N.no•-`
      M-agrees () | nothing

  interpret-return-soundᵢ (suc n) world-agreement (N.no•-ƛ no-N)
      M-agrees refl =
    closure-return-sound no-N M-agrees

  interpret-return-soundᵢ (suc n) {W = W} {γ = γ} {θ = θ}
      {M = L N.· M} world-agreement
      (N.no•-· no-L no-M)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      result-eq
      with interpret W γ θ L n in L-eq
  interpret-return-soundᵢ (suc n) {γ = γ} {θ = θ}
      {M = L N.· M} world-agreement
      (N.no•-· no-L no-M)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      () | timed W₁
  interpret-return-soundᵢ (suc n) {M = L N.· M} world-agreement
      (N.no•-· no-L no-M)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      () | blamed W₁
  interpret-return-soundᵢ (suc n) {M = L N.· M} world-agreement
      (N.no•-· no-L no-M)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      () | failed W₁ e
  interpret-return-soundᵢ (suc n) {γ = γ} {θ = θ}
      {M = L N.· M} world-agreement
      (N.no•-· no-L no-M)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      result-eq | returned W₁ F
      with interpret W₁ γ θ M n in M-eq
  interpret-return-soundᵢ (suc n) world-agreement
      (N.no•-· no-L no-M)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      () | returned W₁ F | timed W₂
  interpret-return-soundᵢ (suc n) world-agreement
      (N.no•-· no-L no-M)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      () | returned W₁ F | blamed W₂
  interpret-return-soundᵢ (suc n) world-agreement
      (N.no•-· no-L no-M)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      () | returned W₁ F | failed W₂ e
  interpret-return-soundᵢ (suc n) world-agreement
      (N.no•-· no-L no-M)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      result-eq | returned W₁ F | returned W₂ U
      with interpret-return-soundᵢ n world-agreement no-L
        (term-trace-agreement τ vs θ-agrees γ-agrees refl) L-eq
  interpret-return-soundᵢ (suc n) world-agreement
      (N.no•-· no-L no-M)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      result-eq | returned W₁ F | returned W₂ U
      | return-trace χL f path-L L-reduction F-agrees
      with interpret-return-soundᵢ n
        (world-trace-agreement-++ world-agreement path-L) no-M
        (term-trace-path-empty world-agreement path-L
          (term-trace-agreement τ vs θ-agrees γ-agrees refl)) M-eq
  interpret-return-soundᵢ (suc n) world-agreement
      (N.no•-· no-L no-M)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      result-eq | returned W₁ F | returned W₂ U
      | return-trace χL f path-L L-reduction F-agrees
      | return-trace χM u path-M M-reduction U-agrees
      with apply-return-soundᵢ n
        (world-trace-agreement-++
          (world-trace-agreement-++ world-agreement path-L) path-M)
        (value-trace-path-empty
          (world-trace-agreement-++ world-agreement path-L)
          path-M F-agrees)
        U-agrees result-eq
  interpret-return-soundᵢ (suc n) world-agreement
      (N.no•-· no-L no-M)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      result-eq | returned W₁ F | returned W₂ U
      | return-trace χL f path-L L-reduction F-agrees
      | return-trace χM u path-M M-reduction U-agrees
      | return-trace χA z path-A A-reduction R-agrees =
    return-trace-start-eq reification
      (assemble-application-return world-agreement path-L path-M path-A
        (reified-term-no-bullet γ-agrees no-M)
        L-reduction F-agrees M-reduction A-reduction R-agrees)

  interpret-return-soundᵢ (suc n) {W = W} {γ = γ} {θ = θ}
      {M = N.Λ V} world-agreement
      (N.no•-Λ no-V) M-agrees result-eq
      with syntacticValue? V
  interpret-return-soundᵢ (suc n) world-agreement
      (N.no•-Λ no-V) M-agrees () | no not-value
  interpret-return-soundᵢ (suc n) {γ = γ} {θ = θ}
      {M = N.Λ V} world-agreement
      (N.no•-Λ no-V) M-agrees result-eq | yes vV
      with closeTypeAbstractionBody vV γ θ in close-eq
  interpret-return-soundᵢ (suc n) world-agreement
      (N.no•-Λ no-V) M-agrees refl | yes vV | just U =
    type-abstraction-return-sound {vV = vV} no-V M-agrees close-eq
  interpret-return-soundᵢ (suc n) world-agreement
      (N.no•-Λ no-V) M-agrees () | yes vV | nothing

  interpret-return-soundᵢ (suc n) {W = W} {γ = γ} {θ = θ}
      {M = N.ν A L c} world-agreement
      (N.no•-ν no-L)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      result-eq
      with interpret W γ θ L n in L-eq
  interpret-return-soundᵢ (suc n) {W = W} {γ = γ} {θ = θ}
      {M = N.ν A L c} {U = U} {V = R} world-agreement
      (N.no•-ν no-L)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      () | timed W₁
  interpret-return-soundᵢ (suc n) {W = W} {γ = γ} {θ = θ}
      {M = N.ν A L c} {U = U} {V = R} world-agreement
      (N.no•-ν no-L)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      () | blamed W₁
  interpret-return-soundᵢ (suc n) {M = N.ν A L c} world-agreement
      (N.no•-ν no-L)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      () | failed W₁ e
  interpret-return-soundᵢ (suc n) {W = W} {γ = γ} {θ = θ}
      {M = N.ν A L c} {U = U} {V = R} world-agreement
      (N.no•-ν no-L)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      result-eq | returned W₁ F =
    return-trace-start-eq reification nu-return
    where
    L-trace = interpret-return-soundᵢ n world-agreement no-L
      (term-trace-agreement τ vs θ-agrees γ-agrees refl) L-eq

    full-result-eq :
      interpret W γ θ (N.ν A L c) (suc n) ≡ returned U R
    full-result-eq rewrite L-eq =
      result-eq

    nu-return : ReturnTrace world-agreement _ _ _
    nu-return with L-trace
    nu-return | return-trace χL f path-L L-reduction F-agrees =
      finish-nu-returnᵢ n world-agreement θ-agrees
        path-L F-agrees L-reduction L-eq full-result-eq

  interpret-return-soundᵢ (suc n) world-agreement N.no•-$
      M-agrees refl =
    constant-return-sound M-agrees

  interpret-return-soundᵢ (suc n) {W = W} {γ = γ} {θ = θ}
      {M = L N.⊕[ op ] M} world-agreement
      (N.no•-⊕ no-L no-M)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      result-eq
      with interpret W γ θ L n in L-eq
  interpret-return-soundᵢ (suc n) {γ = γ} {θ = θ}
      {M = L N.⊕[ op ] M} world-agreement
      (N.no•-⊕ no-L no-M)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      () | timed W₁
  interpret-return-soundᵢ (suc n) {γ = γ} {θ = θ}
      {M = L N.⊕[ op ] M} world-agreement
      (N.no•-⊕ no-L no-M)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      () | blamed W₁
  interpret-return-soundᵢ (suc n) world-agreement
      (N.no•-⊕ no-L no-M)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      () | failed W₁ e
  interpret-return-soundᵢ (suc n) {γ = γ} {θ = θ}
      {M = L N.⊕[ op ] M} world-agreement
      (N.no•-⊕ no-L no-M)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      result-eq | returned W₁ F
      with interpret W₁ γ θ M n in M-eq
  interpret-return-soundᵢ (suc n) world-agreement
      (N.no•-⊕ no-L no-M)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      () | returned W₁ F | timed W₂
  interpret-return-soundᵢ (suc n) world-agreement
      (N.no•-⊕ no-L no-M)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      () | returned W₁ F | blamed W₂
  interpret-return-soundᵢ (suc n) world-agreement
      (N.no•-⊕ no-L no-M)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      () | returned W₁ F | failed W₂ e
  interpret-return-soundᵢ (suc n) world-agreement
      (N.no•-⊕ no-L no-M)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      result-eq | returned W₁ F | returned W₂ U
      with interpret-return-soundᵢ n world-agreement no-L
        (term-trace-agreement τ vs θ-agrees γ-agrees refl) L-eq
  interpret-return-soundᵢ (suc n) world-agreement
      (N.no•-⊕ no-L no-M)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      result-eq | returned W₁ F | returned W₂ U
      | return-trace χL f path-L L-reduction F-agrees
      with interpret-return-soundᵢ n
        (world-trace-agreement-++ world-agreement path-L) no-M
        (term-trace-path-empty world-agreement path-L
          (term-trace-agreement τ vs θ-agrees γ-agrees refl)) M-eq
  interpret-return-soundᵢ (suc n) world-agreement
      (N.no•-⊕ no-L no-M)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      result-eq | returned W₁ F | returned W₂ U
      | return-trace χL f path-L L-reduction F-agrees
      | return-trace χM u path-M M-reduction U-agrees
      with F-agrees | U-agrees
  interpret-return-soundᵢ (suc n)
      {M = L N.⊕[ Primitives.addℕ ] M} world-agreement
      (N.no•-⊕ no-L no-M)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      refl | returned W₁ (constant (Primitives.κℕ m))
           | returned W₂ (constant (Primitives.κℕ k))
      | return-trace χL .(N.$ (Primitives.κℕ m)) path-L L-reduction
          constant-trace-agrees
      | return-trace χM .(N.$ (Primitives.κℕ k)) path-M M-reduction
          constant-trace-agrees
      | constant-trace-agrees | constant-trace-agrees =
    return-trace-start-eq reification
      (return-trace (χL ++ (χM ++ keep ∷ []))
        (N.$ (Primitives.κℕ (m + k)))
        (world-trace-path-++ path-L
          (world-trace-path-++ path-M
            (world-trace-keep world-trace-done)))
        (↠-trans
          (⊕₁-↠ (reified-term-no-bullet γ-agrees no-M) L-reduction)
          (↠-trans
            (⊕₂-↠ (N.$ _) N.no•-$ M-reduction)
            (subst
              (λ q → (q N.⊕[ Primitives.addℕ ] N.$ (Primitives.κℕ k))
                —↠[ keep ∷ [] ] N.$ (Primitives.κℕ (m + k)))
              (sym (applyTerms-const χM (Primitives.κℕ m)))
              (↠-step (pure-step δ-⊕) ↠-refl))))
        constant-trace-agrees)

  interpret-return-soundᵢ (suc n) {W = W} {γ = γ} {θ = θ}
      {M = M N.⟨ c ⟩} world-agreement
      (N.no•-⟨⟩ no-M)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      result-eq
      with interpret W γ θ M n in M-eq
  interpret-return-soundᵢ (suc n) {M = M N.⟨ c ⟩} world-agreement
      (N.no•-⟨⟩ no-M)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      () | timed W₁
  interpret-return-soundᵢ (suc n) {W = W} {γ = γ} {θ = θ}
      {M = M N.⟨ c ⟩} world-agreement (N.no•-⟨⟩ no-M)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      () | blamed W₁
  interpret-return-soundᵢ (suc n) world-agreement
      (N.no•-⟨⟩ no-M)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      () | failed W₁ e
  interpret-return-soundᵢ (suc n) world-agreement
      (N.no•-⟨⟩ no-M)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      result-eq | returned W₁ V
      with interpret-return-soundᵢ n world-agreement no-M
        (term-trace-agreement τ vs θ-agrees γ-agrees refl) M-eq
  interpret-return-soundᵢ (suc n) world-agreement
      (N.no•-⟨⟩ no-M)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      result-eq | returned W₁ V
      | return-trace χM v path-M M-reduction V-agrees
      with type-environment-trace-path world-agreement path-M θ-agrees
  interpret-return-soundᵢ (suc n) {M = M N.⟨ c ⟩} world-agreement
      (N.no•-⟨⟩ no-M)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      result-eq | returned W₁ V
      | return-trace χM v path-M M-reduction V-agrees
      | path-agreement
      with coerce-return-soundᵢ n
        (world-trace-agreement-++ world-agreement path-M)
        (final-agreement path-agreement) V-agrees result-eq
  interpret-return-soundᵢ (suc n) world-agreement
      (N.no•-⟨⟩ no-M)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      result-eq | returned W₁ V
      | return-trace χM v path-M M-reduction V-agrees
      | path-agreement | C-trace =
    return-trace-start-eq reification
      (continue-under-cast world-agreement path-M M-reduction
        (return-trace-start-eq
          (cong (λ d → v N.⟨ d ⟩)
            (sym (coercion-action path-agreement _))) C-trace))

  interpret-return-soundᵢ (suc n) world-agreement N.no•-blame
      M-agrees ()

  finish-nu-returnᵢ n
      {W₁ = world next cells} {θ = θ} {A = A} {c = c}
      {τ = τ} {F = F} {f = f} {χL = χL}
      world-agreement θ-agrees path-L F-agrees L-reduction
      L-eq result-eq
      rewrite L-eq
      with instantiateValue W₂ α F n in inst-eq
    where
    α = seal-name-id next
    W₂ = allocate (world next cells) A θ
  finish-nu-returnᵢ n
      {W₁ = world next cells} {θ = θ} {A = A} {c = c}
      {τ = τ} {F = F} {f = f} {χL = χL}
      world-agreement θ-agrees path-L F-agrees L-reduction
      L-eq () | timed W₃
  finish-nu-returnᵢ n
      {W₁ = world next cells} {θ = θ} {A = A} {c = c}
      {τ = τ} {F = F} {f = f} {χL = χL}
      world-agreement θ-agrees path-L F-agrees L-reduction
      L-eq () | blamed W₃
  finish-nu-returnᵢ n
      {W₁ = world next cells} {θ = θ} {A = A} {c = c}
      {τ = τ} {F = F} {f = f} {χL = χL}
      world-agreement θ-agrees path-L F-agrees L-reduction
      L-eq () | failed W₃ e
  finish-nu-returnᵢ n
      {W₁ = world next cells} {θ = θ} {A = A} {c = c}
      {τ = τ} {F = F} {f = f} {χL = χL}
      world-agreement θ-agrees path-L F-agrees L-reduction
      L-eq result-eq | returned W₃ U
      with coerceValue W₃ (seal-name (seal-name-id next) ∷ θ) c U n
        in coerce-eq
  finish-nu-returnᵢ n
      {W₁ = world next cells} {θ = θ} {A = A} {c = c}
      {τ = τ} {F = F} {f = f} {χL = χL}
      world-agreement θ-agrees path-L F-agrees L-reduction
      L-eq () | returned W₃ U | timed W₄
  finish-nu-returnᵢ n
      {W₁ = world next cells} {θ = θ} {A = A} {c = c}
      {τ = τ} {F = F} {f = f} {χL = χL}
      world-agreement θ-agrees path-L F-agrees L-reduction
      L-eq () | returned W₃ U | blamed W₄
  finish-nu-returnᵢ n
      {W₁ = world next cells} {θ = θ} {A = A} {c = c}
      {τ = τ} {F = F} {f = f} {χL = χL}
      world-agreement θ-agrees path-L F-agrees L-reduction
      L-eq () | returned W₃ U | failed W₄ e
  finish-nu-returnᵢ n
      {W₁ = world next cells} {θ = θ} {A = A} {c = c}
      {τ = τ} {F = F} {f = f} {χL = χL}
      world-agreement θ-agrees path-L F-agrees L-reduction
      L-eq refl | returned W₃ U | returned W₄ R
      with type-environment-trace-path world-agreement path-L θ-agrees
  finish-nu-returnᵢ n
      {W₁ = world next cells} {θ = θ} {A = A} {c = c}
      {τ = τ} {F = F} {f = f} {χL = χL}
      world-agreement θ-agrees path-L F-agrees L-reduction
      L-eq refl | returned W₃ U | returned W₄ R
      | path-agreement-L
      with instantiate-return-soundᵢ n
        {W = allocate (world next cells) A θ}
        {α = seal-name-id next} {F = F}
        agreement-B newest-lookup F-after-bind inst-eq
    where
    agreement-L = world-trace-agreement-++ world-agreement path-L
    A₁ = applyTys χL (renameᵗ τ A)
    c₁ = applyCoercionUnderTyBinders χL (C.renameᶜ (extᵗ τ) c)
    canonical-bind = allocation-path {A = A} agreement-L
      (final-agreement path-agreement-L)
    path-B = subst
      (λ B → WorldTracePath (world next cells) (bind B ∷ [])
        (allocate (world next cells) A θ))
      (type-action path-agreement-L A) canonical-bind
    agreement-B = world-trace-agreement-++ agreement-L path-B
    F-after-bind = value-trace-path-empty agreement-L path-B F-agrees
    newest-lookup = new-seal-lookup []
      {next = next} {cells = cells} {A = A} {θ = θ}
  finish-nu-returnᵢ n
      {W₁ = world next cells} {θ = θ} {A = A} {c = c}
      {τ = τ} {F = F} {f = f} {χL = χL}
      world-agreement θ-agrees path-L F-agrees L-reduction
      L-eq refl | returned W₃ U | returned W₄ R
      | path-agreement-L
      | return-trace χI u path-I I-reduction U-agrees
      with type-environment-trace-path agreement-B path-I
        extended-agreement
    where
    agreement-L = world-trace-agreement-++ world-agreement path-L
    canonical-bind = allocation-path {A = A} agreement-L
      (final-agreement path-agreement-L)
    path-B = subst
      (λ B → WorldTracePath (world next cells) (bind B ∷ [])
        (allocate (world next cells) A θ))
      (type-action path-agreement-L A) canonical-bind
    agreement-B = world-trace-agreement-++ agreement-L path-B
    outer-after-bind = type-environment-trace-bind
      {new-agreement = agreement-B} (final-agreement path-agreement-L)
    extended-agreement = type-environment-instantiate-head
      (new-seal-lookup []
        {next = next} {cells = cells} {A = A} {θ = θ})
      outer-after-bind
  finish-nu-returnᵢ n
      {W₁ = world next cells} {θ = θ} {A = A} {c = c}
      {τ = τ} {F = F} {f = f} {χL = χL}
      world-agreement θ-agrees path-L F-agrees L-reduction
      L-eq refl | returned W₃ U | returned W₄ R
      | path-agreement-L
      | return-trace χI u path-I I-reduction U-agrees
      | path-agreement-I
      with coerce-return-soundᵢ n agreement-I
        (final-agreement path-agreement-I) U-agrees coerce-eq
    where
    agreement-L = world-trace-agreement-++ world-agreement path-L
    canonical-bind = allocation-path {A = A} agreement-L
      (final-agreement path-agreement-L)
    path-B = subst
      (λ B → WorldTracePath (world next cells) (bind B ∷ [])
        (allocate (world next cells) A θ))
      (type-action path-agreement-L A) canonical-bind
    agreement-B = world-trace-agreement-++ agreement-L path-B
    agreement-I = world-trace-agreement-++ agreement-B path-I
  finish-nu-returnᵢ n
      {W₁ = world next cells} {θ = θ} {A = A} {c = c}
      {τ = τ} {PL = PL} {F = F} {f = f} {χL = χL}
      world-agreement θ-agrees path-L F-agrees L-reduction
      L-eq refl | returned W₃ U | returned W₄ R
      | path-agreement-L
      | return-trace χI u path-I I-reduction U-agrees
      | path-agreement-I | C-trace
      with continue-under-cast agreement-B path-I I-reduction
        (return-trace-start-eq c-start-eq C-trace)
    where
    agreement-L = world-trace-agreement-++ world-agreement path-L
    canonical-bind = allocation-path {A = A} agreement-L
      (final-agreement path-agreement-L)
    path-B = subst
      (λ B → WorldTracePath (world next cells) (bind B ∷ [])
        (allocate (world next cells) A θ))
      (type-action path-agreement-L A) canonical-bind
    agreement-B = world-trace-agreement-++ agreement-L path-B
    c-start-eq = cong (λ d → u N.⟨ d ⟩)
      (sym
        (trans (coercion-action path-agreement-I c)
          (cong (applyCoercions χI)
            (trans
              (renameᶜ-cong
                (extend-after-insertion (final-renaming path-agreement-L)) c)
              (binder-coercion-action path-agreement-L c)))))
  finish-nu-returnᵢ n
      {W₁ = world next cells} {θ = θ} {A = A} {c = c}
      {τ = τ} {PL = PL} {F = F} {f = f} {χL = χL}
      world-agreement θ-agrees path-L F-agrees L-reduction
      L-eq refl | returned W₃ U | returned W₄ R
      | path-agreement-L
      | return-trace χI u path-I I-reduction U-agrees
      | path-agreement-I | C-trace
      | return-trace χR r path-R R-reduction R-agrees =
    return-trace (χL ++ (bind A₁ ∷ χR)) r
      (world-trace-path-++ path-L
        (world-trace-path-++ path-B path-R))
      (↠-trans (ν-↠ L-reduction)
        (↠-step
          (ν-step (value-trace-value F-agrees)
            (value-trace-no-bullet F-agrees)) R-reduction))
      (value-trace-rebase R-agrees)
    where
    agreement-L = world-trace-agreement-++ world-agreement path-L
    A₁ = applyTys χL (renameᵗ τ A)
    c₁ = applyCoercionUnderTyBinders χL (C.renameᶜ (extᵗ τ) c)
    canonical-bind = allocation-path {A = A} agreement-L
      (final-agreement path-agreement-L)
    path-B = subst
      (λ B → WorldTracePath (world next cells) (bind B ∷ [])
        (allocate (world next cells) A θ))
      (type-action path-agreement-L A) canonical-bind
    agreement-B = world-trace-agreement-++ agreement-L path-B
    c-start-eq = cong (λ d → u N.⟨ d ⟩)
      (sym
        (trans (coercion-action path-agreement-I c)
          (cong (applyCoercions χI)
            (trans
              (renameᶜ-cong
                (extend-after-insertion (final-renaming path-agreement-L)) c)
              (binder-coercion-action path-agreement-L c)))))

  apply-return-soundᵢ zero world-agreement F-agrees U-agrees ()
  apply-return-soundᵢ (suc n) world-agreement
      (closure-trace-agrees
        {M = M} {M′ = body} {γ = γ} {θ = θ} {τ = τ} {vs = vs}
        θ-agrees γ-agrees no-M reification no-body)
      U-agrees result-eq
      with interpret-return-soundᵢ n world-agreement no-M
        (term-trace-agreement τ (_ ∷ vs) θ-agrees
          (environment-cons-trace-agrees U-agrees γ-agrees) refl)
        result-eq
  apply-return-soundᵢ (suc n) world-agreement
      (closure-trace-agrees
        {M = M} {M′ = body} {γ = γ} {θ = θ} {τ = τ} {vs = vs}
        θ-agrees γ-agrees no-M reification no-body)
      U-agrees result-eq | body-trace =
    closure-application-from-body
      {M = M} {body = body} {τ = τ} {vs = vs}
      reification U-agrees body-trace

  apply-return-soundᵢ (suc n) world-agreement
      constant-trace-agrees U-agrees ()
  apply-return-soundᵢ (suc n) world-agreement
      (tagged-trace-agrees θ-agrees F-agrees) U-agrees ()
  apply-return-soundᵢ (suc n) world-agreement
      (sealed-trace-agrees name-eq F-agrees) U-agrees ()
  apply-return-soundᵢ (suc n) {W = W}
      {F = function-proxy p q θ V} {U = U} world-agreement
      (function-proxy-trace-agrees θ-agrees F-agrees)
      U-agrees result-eq
      with coerceValue W θ p U n in p-eq
  apply-return-soundᵢ (suc n) world-agreement
      (function-proxy-trace-agrees θ-agrees F-agrees)
      U-agrees () | timed W₁
  apply-return-soundᵢ (suc n) world-agreement
      (function-proxy-trace-agrees θ-agrees F-agrees)
      U-agrees () | blamed W₁
  apply-return-soundᵢ (suc n) world-agreement
      (function-proxy-trace-agrees θ-agrees F-agrees)
      U-agrees () | failed W₁ e
  apply-return-soundᵢ (suc n) {F = function-proxy p q θ V}
      world-agreement
      (function-proxy-trace-agrees θ-agrees F-agrees)
      U-agrees result-eq | returned W₁ U′
      with applyValue W₁ V U′ n in apply-eq
  apply-return-soundᵢ (suc n) world-agreement
      (function-proxy-trace-agrees θ-agrees F-agrees)
      U-agrees () | returned W₁ U′ | timed W₂
  apply-return-soundᵢ (suc n) world-agreement
      (function-proxy-trace-agrees θ-agrees F-agrees)
      U-agrees () | returned W₁ U′ | blamed W₂
  apply-return-soundᵢ (suc n) world-agreement
      (function-proxy-trace-agrees θ-agrees F-agrees)
      U-agrees () | returned W₁ U′ | failed W₂ e
  apply-return-soundᵢ (suc n) world-agreement
      (function-proxy-trace-agrees {p = p} {q = q}
        θ-agrees F-agrees)
      U-agrees result-eq | returned W₁ U′ | returned W₂ V′
      with coerce-return-soundᵢ n world-agreement θ-agrees U-agrees p-eq
  apply-return-soundᵢ (suc n) world-agreement
      (function-proxy-trace-agrees {p = p} {q = q}
        θ-agrees F-agrees)
      U-agrees result-eq | returned W₁ U′ | returned W₂ V′
      | return-trace χP u′ path-P P-reduction U′-agrees
      with apply-return-soundᵢ n
        (world-trace-agreement-++ world-agreement path-P)
        (value-trace-path-empty world-agreement path-P F-agrees)
        U′-agrees apply-eq
  apply-return-soundᵢ (suc n) world-agreement
      (function-proxy-trace-agrees {p = p} {q = q}
        θ-agrees F-agrees)
      U-agrees result-eq | returned W₁ U′ | returned W₂ V′
      | return-trace χP u′ path-P P-reduction U′-agrees
      | return-trace χA z path-A A-reduction V′-agrees
      with type-environment-trace-path world-agreement
        (world-trace-path-++ path-P path-A) θ-agrees
  apply-return-soundᵢ (suc n) world-agreement
      (function-proxy-trace-agrees {p = p} {q = q}
        θ-agrees F-agrees)
      U-agrees result-eq | returned W₁ U′ | returned W₂ V′
      | return-trace χP u′ path-P P-reduction U′-agrees
      | return-trace χA z path-A A-reduction V′-agrees
      | path-agreement
      with coerce-return-soundᵢ n
        (world-trace-agreement-++ world-agreement
          (world-trace-path-++ path-P path-A))
        (final-agreement path-agreement)
        (value-trace-rebase V′-agrees) result-eq
  apply-return-soundᵢ (suc n) world-agreement
      (function-proxy-trace-agrees {p = p} {q = q}
        θ-agrees F-agrees)
      U-agrees result-eq | returned W₁ U′ | returned W₂ V′
      | return-trace χP u′ path-P P-reduction U′-agrees
      | return-trace χA z path-A A-reduction V′-agrees
      | path-agreement | Q-trace =
    prepend-pure-step
      (β-↦ (value-trace-value F-agrees) (value-trace-value U-agrees))
      (continue-under-cast world-agreement
        (world-trace-path-++ path-P path-A)
        (↠-trans
          (·₂-↠ (value-trace-value F-agrees)
            (value-trace-no-bullet F-agrees) P-reduction)
          A-reduction)
        (return-trace-start-eq
          (cong (λ d → z N.⟨ d ⟩)
            (sym (coercion-action path-agreement q))) Q-trace))
  apply-return-soundᵢ (suc n) world-agreement
      (type-abstraction-trace-agrees fresh graph θ-agrees γ-agrees
        no-raw reification vP no-P) U-agrees ()
  apply-return-soundᵢ (suc n) world-agreement
      (forall-proxy-trace-agrees θ-agrees F-agrees) U-agrees ()
  apply-return-soundᵢ (suc n) world-agreement
      (generalized-trace-agrees θ-agrees F-agrees) U-agrees ()

  instantiate-return-soundᵢ zero world-agreement newest F-agrees ()
  instantiate-return-soundᵢ (suc n) world-agreement newest
      (type-abstraction-trace-agrees fresh graph θ-agrees γ-agrees
        no-raw reification vP no-P) refl =
    type-abstraction-instantiation-return-sound newest
      (type-abstraction-trace-agrees fresh graph θ-agrees γ-agrees
        no-raw reification vP no-P)
  instantiate-return-soundᵢ (suc n) {W = W} {α = α}
      {F = forall-proxy c θ V} world-agreement newest
      (forall-proxy-trace-agrees {c = c} θ-agrees F-agrees)
      result-eq
      with instantiateValue W α V n in inst-eq
  instantiate-return-soundᵢ (suc n) world-agreement newest
      (forall-proxy-trace-agrees θ-agrees F-agrees) () | timed W₁
  instantiate-return-soundᵢ (suc n) world-agreement newest
      (forall-proxy-trace-agrees θ-agrees F-agrees) () | blamed W₁
  instantiate-return-soundᵢ (suc n) world-agreement newest
      (forall-proxy-trace-agrees θ-agrees F-agrees) () | failed W₁ e
  instantiate-return-soundᵢ (suc n) world-agreement newest
      (forall-proxy-trace-agrees {c = c} θ-agrees F-agrees)
      result-eq | returned W₁ U
      with instantiate-return-soundᵢ n world-agreement newest F-agrees inst-eq
  instantiate-return-soundᵢ (suc n) world-agreement newest
      (forall-proxy-trace-agrees {c = c} θ-agrees F-agrees)
      result-eq | returned W₁ U
      | return-trace χI u path-I I-reduction U-agrees
      with type-environment-trace-path world-agreement path-I
        (type-environment-instantiate-head newest θ-agrees)
  instantiate-return-soundᵢ (suc n) world-agreement newest
      (forall-proxy-trace-agrees {c = c} θ-agrees F-agrees)
      result-eq | returned W₁ U
      | return-trace χI u path-I I-reduction U-agrees
      | path-agreement
      with coerce-return-soundᵢ n
        (world-trace-agreement-++ world-agreement path-I)
        (final-agreement path-agreement) U-agrees result-eq
  instantiate-return-soundᵢ (suc n) world-agreement newest
      (forall-proxy-trace-agrees {c = c} θ-agrees F-agrees)
      result-eq | returned W₁ U
      | return-trace χI u path-I I-reduction U-agrees
      | path-agreement | C-trace =
    prepend-pure-step (β-∀• (value-trace-value F-agrees))
      (return-trace-start-eq
        (cong (λ d → (N._• _) N.⟨ d ⟩)
          (open-extended-coercion _ c))
        (continue-under-cast world-agreement path-I I-reduction
          (return-trace-start-eq
            (cong (λ d → u N.⟨ d ⟩)
              (sym (coercion-action path-agreement c))) C-trace)))
  instantiate-return-soundᵢ (suc n) world-agreement newest
      (generalized-trace-agrees {c = c} θ-agrees F-agrees) result-eq
      with coerce-return-soundᵢ n world-agreement
        (type-environment-instantiate-head newest θ-agrees)
        F-agrees result-eq
  instantiate-return-soundᵢ (suc n) world-agreement newest
      (generalized-trace-agrees {c = c} θ-agrees F-agrees) result-eq
      | C-trace =
    prepend-pure-step (β-gen• (value-trace-value F-agrees))
      (return-trace-start-eq
        (cong (λ d → _ N.⟨ d ⟩) (open-extended-coercion _ c)) C-trace)
  instantiate-return-soundᵢ (suc n) world-agreement newest
      (closure-trace-agrees θ-agrees γ-agrees no-raw reification no-body) ()
  instantiate-return-soundᵢ (suc n) world-agreement newest
      constant-trace-agrees ()
  instantiate-return-soundᵢ (suc n) world-agreement newest
      (tagged-trace-agrees θ-agrees F-agrees) ()
  instantiate-return-soundᵢ (suc n) world-agreement newest
      (sealed-trace-agrees name-eq F-agrees) ()
  instantiate-return-soundᵢ (suc n) world-agreement newest
      (function-proxy-trace-agrees θ-agrees F-agrees) ()

  coerce-return-soundᵢ zero world-agreement θ-agrees V-agrees ()
  coerce-return-soundᵢ (suc n) world-agreement θ-agrees V-agrees
      {c = C.id A} refl =
    identity-return-sound V-agrees
  coerce-return-soundᵢ (suc n) {W = W} {θ = θ} {V = V}
      world-agreement θ-agrees V-agrees
      {c = c C.︔ d} result-eq
      with coerceValue W θ c V n in c-eq
  coerce-return-soundᵢ (suc n) world-agreement θ-agrees V-agrees
      {c = c C.︔ d} () | timed W₁
  coerce-return-soundᵢ (suc n) world-agreement θ-agrees V-agrees
      {c = c C.︔ d} () | blamed W₁
  coerce-return-soundᵢ (suc n) world-agreement θ-agrees V-agrees
      {c = c C.︔ d} () | failed W₁ e
  coerce-return-soundᵢ (suc n) {W = W} {θ = θ} {V = V}
      world-agreement θ-agrees V-agrees
      {c = c C.︔ d} result-eq | returned W₁ U
      with coerce-return-soundᵢ n world-agreement θ-agrees V-agrees c-eq
  coerce-return-soundᵢ (suc n) world-agreement θ-agrees V-agrees
      {c = c C.︔ d} result-eq | returned W₁ U
      | return-trace χC u path-C C-reduction U-agrees
      with type-environment-trace-path world-agreement path-C θ-agrees
  coerce-return-soundᵢ (suc n) {W = W} {θ = θ} {V = V}
      world-agreement θ-agrees V-agrees
      {c = c C.︔ d} result-eq | returned W₁ U
      | return-trace χC u path-C C-reduction U-agrees
      | path-agreement
      with coerce-return-soundᵢ n
        (world-trace-agreement-++ world-agreement path-C)
        (final-agreement path-agreement) U-agrees
        result-eq
  coerce-return-soundᵢ (suc n) world-agreement θ-agrees V-agrees
      {c = c C.︔ d} result-eq | returned W₁ U
      | return-trace χC u path-C C-reduction U-agrees
      | path-agreement | D-trace =
    prepend-pure-step (β-seq (value-trace-value V-agrees))
      (continue-under-cast world-agreement path-C C-reduction
        (return-trace-start-eq
          (cong (λ q → u N.⟨ q ⟩)
            (sym (coercion-action path-agreement d))) D-trace))
  coerce-return-soundᵢ (suc n) world-agreement θ-agrees V-agrees
      {c = p C.↦ q} refl =
    function-proxy-return-sound θ-agrees V-agrees
  coerce-return-soundᵢ (suc n) world-agreement θ-agrees V-agrees
      {c = C.`∀ c} refl =
    forall-proxy-return-sound θ-agrees V-agrees
  coerce-return-soundᵢ (suc n) {W = W} {θ = θ} {V = V}
      world-agreement θ-agrees V-agrees
      {c = G C.!} result-eq
      with ground? θ G in ground-eq
  coerce-return-soundᵢ (suc n) world-agreement θ-agrees V-agrees
      {c = G C.!} () | no not-ground
  coerce-return-soundᵢ (suc n) {θ = θ} world-agreement θ-agrees V-agrees
      {c = G C.!} result-eq | yes runtime-ground
      with tagOf θ (runtime-ground-syntax runtime-ground) in tag-eq
  coerce-return-soundᵢ (suc n) {W = W} {θ = θ} {V = V}
      world-agreement θ-agrees V-agrees
      {c = G C.!} result-eq | yes runtime-ground | just tag =
    return-trace-result-eq
      result-eq
      (tag-return-sound runtime-ground θ-agrees V-agrees)
  coerce-return-soundᵢ (suc n) world-agreement θ-agrees V-agrees
      {c = G C.!} () | yes runtime-ground | nothing
  coerce-return-soundᵢ (suc n) {W = W} {θ = θ}
      world-agreement θ-agrees V-agrees
      {c = G C.？} result-eq
      with ground? θ G in ground-eq
  coerce-return-soundᵢ (suc n) world-agreement θ-agrees V-agrees
      {c = G C.？} () | no not-ground
  coerce-return-soundᵢ (suc n) {θ = θ} world-agreement θ-agrees V-agrees
      {c = G C.？} result-eq | yes runtime-ground
      with tagOf θ (runtime-ground-syntax runtime-ground) in expected-eq
  coerce-return-soundᵢ (suc n) world-agreement θ-agrees V-agrees
      {c = G C.？} () | yes runtime-ground | nothing
  coerce-return-soundᵢ (suc n) world-agreement θ-agrees
      (tagged-trace-agrees {G = H} {gG = gH} {θ = σ}
        σ-agrees U-agrees)
      {c = G C.？} result-eq | yes runtime-ground | just expected
      with tagOf σ gH in actual-eq
  coerce-return-soundᵢ (suc n) world-agreement θ-agrees
      (tagged-trace-agrees σ-agrees U-agrees)
      {c = G C.？} () | yes runtime-ground | just expected | nothing
  coerce-return-soundᵢ (suc n) world-agreement θ-agrees
      (tagged-trace-agrees {G = H} {gG = gH} σ-agrees U-agrees)
      {c = G C.？} result-eq | yes runtime-ground | just expected
      | just actual
      with expected ≟Tag actual
  coerce-return-soundᵢ (suc n) {W = W} {θ = θ} world-agreement θ-agrees
      (tagged-trace-agrees {G = H} {gG = gH} {θ = σ} {V = U}
        σ-agrees U-agrees)
      {c = G C.？} result-eq | yes runtime-ground | just expected
      | just .expected | yes refl =
    return-trace-result-eq
      result-eq
      (untag-return-sound
        {G = G} {H = H} {θ = θ} {σ = σ}
        {runtime-ground = runtime-ground} {gH = gH}
        θ-agrees σ-agrees U-agrees
        expected-eq actual-eq refl)
  coerce-return-soundᵢ (suc n) world-agreement θ-agrees
      (tagged-trace-agrees σ-agrees U-agrees)
      {c = G C.？} () | yes runtime-ground | just expected
      | just actual | no mismatch
  coerce-return-soundᵢ (suc n) world-agreement θ-agrees
      (closure-trace-agrees θ′-agrees γ-agrees no-raw reification no-body)
      {c = G C.？} () | yes runtime-ground | just expected
  coerce-return-soundᵢ (suc n) world-agreement θ-agrees
      constant-trace-agrees {c = G C.？} ()
      | yes runtime-ground | just expected
  coerce-return-soundᵢ (suc n) world-agreement θ-agrees
      (sealed-trace-agrees name-eq U-agrees) {c = G C.？} ()
      | yes runtime-ground | just expected
  coerce-return-soundᵢ (suc n) world-agreement θ-agrees
      (function-proxy-trace-agrees θ′-agrees U-agrees)
      {c = G C.？} () | yes runtime-ground | just expected
  coerce-return-soundᵢ (suc n) world-agreement θ-agrees
      (type-abstraction-trace-agrees fresh graph θ′-agrees γ-agrees
        no-raw reification vP no-P)
      {c = G C.？} () | yes runtime-ground | just expected
  coerce-return-soundᵢ (suc n) world-agreement θ-agrees
      (forall-proxy-trace-agrees θ′-agrees U-agrees)
      {c = G C.？} () | yes runtime-ground | just expected
  coerce-return-soundᵢ (suc n) world-agreement θ-agrees
      (generalized-trace-agrees θ′-agrees U-agrees)
      {c = G C.？} () | yes runtime-ground | just expected
  coerce-return-soundᵢ (suc n) {W = W} {θ = θ} {V = V}
      world-agreement θ-agrees V-agrees
      {c = C.seal A X} result-eq
      with lookup θ X in lookup-eq
  coerce-return-soundᵢ (suc n) {W = W} {θ = θ} {V = V}
      world-agreement θ-agrees V-agrees
      {c = C.seal A X} result-eq | just (seal-name α) =
    return-trace-result-eq
      result-eq
      (seal-return-sound lookup-eq θ-agrees V-agrees)
  coerce-return-soundᵢ (suc n) world-agreement θ-agrees V-agrees
      {c = C.seal A X} () | just (abstract-name Y)
  coerce-return-soundᵢ (suc n) world-agreement θ-agrees V-agrees
      {c = C.seal A X} () | nothing
  coerce-return-soundᵢ (suc n) {W = W} {θ = θ}
      world-agreement θ-agrees V-agrees
      {c = C.unseal X A} result-eq
      with lookup θ X in lookup-eq
  coerce-return-soundᵢ (suc n) world-agreement θ-agrees V-agrees
      {c = C.unseal X A} () | nothing
  coerce-return-soundᵢ (suc n) world-agreement θ-agrees V-agrees
      {c = C.unseal X A} () | just (abstract-name Y)
  coerce-return-soundᵢ (suc n) world-agreement θ-agrees
      (sealed-trace-agrees {α = β} name-eq U-agrees)
      {c = C.unseal X A} result-eq | just (seal-name α)
      with α ≟SealName β
  coerce-return-soundᵢ (suc n) {W = W} {θ = θ} world-agreement θ-agrees
      (sealed-trace-agrees {α = β} {V = U} name-eq U-agrees)
      {c = C.unseal X A} result-eq | just (seal-name α) | yes refl =
    return-trace-result-eq
      result-eq
      (unseal-return-sound lookup-eq θ-agrees
        name-eq U-agrees)
  coerce-return-soundᵢ (suc n) world-agreement θ-agrees
      (sealed-trace-agrees name-eq U-agrees)
      {c = C.unseal X A} () | just (seal-name α) | no mismatch
  coerce-return-soundᵢ (suc n) world-agreement θ-agrees
      (closure-trace-agrees θ′-agrees γ-agrees no-raw reification no-body)
      {c = C.unseal X A} () | just (seal-name α)
  coerce-return-soundᵢ (suc n) world-agreement θ-agrees
      constant-trace-agrees {c = C.unseal X A} () | just (seal-name α)
  coerce-return-soundᵢ (suc n) world-agreement θ-agrees
      (tagged-trace-agrees θ′-agrees U-agrees)
      {c = C.unseal X A} () | just (seal-name α)
  coerce-return-soundᵢ (suc n) world-agreement θ-agrees
      (function-proxy-trace-agrees θ′-agrees U-agrees)
      {c = C.unseal X A} () | just (seal-name α)
  coerce-return-soundᵢ (suc n) world-agreement θ-agrees
      (type-abstraction-trace-agrees fresh graph θ′-agrees γ-agrees
        no-raw reification vP no-P)
      {c = C.unseal X A} () | just (seal-name α)
  coerce-return-soundᵢ (suc n) world-agreement θ-agrees
      (forall-proxy-trace-agrees θ′-agrees U-agrees)
      {c = C.unseal X A} () | just (seal-name α)
  coerce-return-soundᵢ (suc n) world-agreement θ-agrees
      (generalized-trace-agrees θ′-agrees U-agrees)
      {c = C.unseal X A} () | just (seal-name α)
  coerce-return-soundᵢ (suc n) world-agreement θ-agrees V-agrees
      {c = C.gen A c} refl =
    generalized-return-sound θ-agrees V-agrees
  coerce-return-soundᵢ (suc n)
      {W = world next cells} {θ = θ} {τ = τ} {V = V} {v = v}
      world-agreement θ-agrees V-agrees
      {c = C.inst B c} result-eq
      with instantiateValue
        (allocate (world next cells) ★ θ) (seal-name-id next) V n
        in inst-eq
  coerce-return-soundᵢ (suc n)
      {W = world next cells} {θ = θ} {τ = τ} {V = V} {v = v}
      world-agreement θ-agrees V-agrees
      {c = C.inst B c} () | timed W₃
  coerce-return-soundᵢ (suc n)
      {W = world next cells} {θ = θ} {τ = τ} {V = V} {v = v}
      world-agreement θ-agrees V-agrees
      {c = C.inst B c} () | blamed W₃
  coerce-return-soundᵢ (suc n)
      {W = world next cells} {θ = θ} {τ = τ} {V = V} {v = v}
      world-agreement θ-agrees V-agrees
      {c = C.inst B c} () | failed W₃ e
  coerce-return-soundᵢ (suc n)
      {W = world next cells} {θ = θ} {τ = τ} {V = V} {v = v}
      world-agreement θ-agrees V-agrees
      {c = C.inst B c} result-eq | returned W₃ U
      with coerceValue W₃ (seal-name (seal-name-id next) ∷ θ) c U n
        in coerce-eq
  coerce-return-soundᵢ (suc n)
      {W = world next cells} {θ = θ} {τ = τ} {V = V} {v = v}
      world-agreement θ-agrees V-agrees
      {c = C.inst B c} () | returned W₃ U | timed W₄
  coerce-return-soundᵢ (suc n)
      {W = world next cells} {θ = θ} {τ = τ} {V = V} {v = v}
      world-agreement θ-agrees V-agrees
      {c = C.inst B c} () | returned W₃ U | blamed W₄
  coerce-return-soundᵢ (suc n)
      {W = world next cells} {θ = θ} {τ = τ} {V = V} {v = v}
      world-agreement θ-agrees V-agrees
      {c = C.inst B c} () | returned W₃ U | failed W₄ e
  coerce-return-soundᵢ (suc n)
      {W = world next cells} {θ = θ} {τ = τ} {V = V} {v = v}
      world-agreement θ-agrees V-agrees
      {c = C.inst B c} result-eq | returned W₃ U | returned W₄ R
      with instantiate-return-soundᵢ n
        {W = allocate (world next cells) ★ θ}
        {α = seal-name-id next} {F = V}
        agreement-B newest-lookup V-after-bind inst-eq
    where
    path-B = allocation-path {A = ★} world-agreement θ-agrees
    agreement-B = world-trace-agreement-++ world-agreement path-B
    V-after-bind = value-trace-path-empty
      world-agreement path-B V-agrees
    newest-lookup = new-seal-lookup []
      {next = next} {cells = cells} {A = ★} {θ = θ}
  coerce-return-soundᵢ (suc n)
      {W = world next cells} {θ = θ} {τ = τ} {V = V} {v = v}
      world-agreement θ-agrees V-agrees
      {c = C.inst B c} result-eq | returned W₃ U | returned W₄ R
      | return-trace χI u path-I I-reduction U-agrees
      with type-environment-trace-path agreement-B path-I
        extended-agreement
    where
    path-B = allocation-path {A = ★} world-agreement θ-agrees
    agreement-B = world-trace-agreement-++ world-agreement path-B
    outer-after-bind = type-environment-trace-bind
      {new-agreement = agreement-B} θ-agrees
    extended-agreement = type-environment-instantiate-head
      (new-seal-lookup []
        {next = next} {cells = cells} {A = ★} {θ = θ})
      outer-after-bind
  coerce-return-soundᵢ (suc n)
      {W = world next cells} {θ = θ} {τ = τ} {V = V} {v = v}
      world-agreement θ-agrees V-agrees
      {c = C.inst B c} result-eq | returned W₃ U | returned W₄ R
      | return-trace χI u path-I I-reduction U-agrees
      | path-agreement-I
      with coerce-return-soundᵢ n agreement-I
        (final-agreement path-agreement-I) U-agrees coerce-eq
    where
    path-B = allocation-path {A = ★} world-agreement θ-agrees
    agreement-B = world-trace-agreement-++ world-agreement path-B
    agreement-I = world-trace-agreement-++ agreement-B path-I
  coerce-return-soundᵢ (suc n)
      {W = world next cells} {θ = θ} {τ = τ} {V = V} {v = v}
      world-agreement θ-agrees V-agrees
      {c = C.inst B c} result-eq | returned W₃ U | returned W₄ R
      | return-trace χI u path-I I-reduction U-agrees
      | path-agreement-I | C-trace
      with continue-under-cast agreement-B path-I I-reduction
        (return-trace-start-eq c-start-eq C-trace)
    where
    path-B = allocation-path {A = ★} world-agreement θ-agrees
    agreement-B = world-trace-agreement-++ world-agreement path-B
    c-start-eq = cong (λ d → u N.⟨ d ⟩)
      (sym
        (trans (coercion-action path-agreement-I c)
          (cong (applyCoercions χI)
            (renameᶜ-cong (extend-after-insertion τ) c))))
  coerce-return-soundᵢ (suc n)
      {W = world next cells} {θ = θ} {τ = τ} {V = V} {v = v}
      world-agreement θ-agrees V-agrees
      {c = C.inst B c} result-eq | returned W₃ U | returned W₄ R
      | return-trace χI u path-I I-reduction U-agrees
      | path-agreement-I | C-trace
      | return-trace χR r path-R R-reduction R-agrees =
    return-trace-result-eq result-eq
      (prepend-pure-step (β-inst (value-trace-value V-agrees))
        (return-trace (bind ★ ∷ χR) r
          (world-trace-path-++ path-B path-R)
          (↠-step
            (ν-step (value-trace-value V-agrees)
              (value-trace-no-bullet V-agrees)) R-reduction)
          (value-trace-rebase R-agrees)))
    where
    path-B = allocation-path {A = ★} world-agreement θ-agrees

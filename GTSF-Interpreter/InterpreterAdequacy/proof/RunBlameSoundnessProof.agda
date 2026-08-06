module InterpreterAdequacy.proof.RunBlameSoundnessProof where

-- File Charter:
--   * Proves successful direct-interpreter blame results sound with respect
--     to the Nu small-step semantics by induction on interpreter fuel.
--   * Reuses return soundness for every recursively successful subcall and
--     simulates only blame-producing branches mutually.
--   * Retains exact allocation traces and uses no progress, preservation,
--     evaluator, or DGG theorem.

open import Agda.Builtin.Equality using (_≡_; refl)
import Data.Empty
open import Data.List using ([]; _∷_; _++_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (zero; suc)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)

import Coercions as C
open import Interpreter
open import InterpreterAdequacy.TraceAgreement
open import InterpreterAdequacy.proof.AllocationTrace using
  (allocation-path)
open import InterpreterAdequacy.proof.BlameTrace
open import InterpreterAdequacy.proof.BlameTraceContinuation
open import InterpreterAdequacy.proof.ClosureApplicationBlameSoundness using
  (closure-application-from-body-blame)
open import InterpreterAdequacy.proof.CoercionBlameSoundness using
  (untag-blame-sound)
open import InterpreterAdequacy.proof.PrimitiveBlameImpossible using
  (apply-primitive-not-blamed)
open import InterpreterAdequacy.proof.ReturnTrace
open import InterpreterAdequacy.proof.RunReturnSoundnessProof using
  ( interpret-return-soundᵢ
  ; apply-return-soundᵢ
  ; instantiate-return-soundᵢ
  ; coerce-return-soundᵢ
  )
open import InterpreterAdequacy.proof.SyntaxReification using
  (reified-term-no-bullet)
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
  using (type-environment-instantiate-head)
open import InterpreterAdequacy.proof.TypeEnvironmentTracePath
open import NuReduction using
  ( applyTerms
  ; applyTys
  ; bind
  ; keep
  ; pure-step
  ; ν-step
  ; β-↦
  ; β-∀•
  ; β-gen•
  ; β-inst
  ; β-seq
  ; tag-untag-bad
  ; ↠-refl
  ; ↠-step
  ; _—↠[_]_
  )
import NuTerms as N
open import proof.Core.Properties.CoercionProperties using
  (renameᶜ-cong)
open import proof.Core.Properties.ReductionProperties using
  ( applyCoercions
  ; applyCoercionUnderTyBinders
  ; cast-↠
  ; ν-↠
  ; ↠-trans
  )
open import Types using (extᵗ; renameᵗ; ★)

mutual
  interpret-blame-soundᵢ :
    ∀ n {W prefix γ θ M P U}
      (world-agreement : WorldTraceAgreement W prefix) →
    N.No• M →
    TermTraceAgreement world-agreement [] γ θ M P →
    interpret W γ θ M n ≡ blamed U →
    BlameTrace world-agreement P U

  apply-blame-soundᵢ :
    ∀ n {W prefix F f U u Z}
      (world-agreement : WorldTraceAgreement W prefix) →
    ValueTraceAgreement world-agreement [] F f →
    ValueTraceAgreement world-agreement [] U u →
    applyValue W F U n ≡ blamed Z →
    BlameTrace world-agreement (f N.· u) Z

  instantiate-blame-soundᵢ :
    ∀ n {W prefix α F f Z}
      (world-agreement : WorldTraceAgreement W prefix) →
    lookup (visibleTypeNames [] W) zero ≡ just (seal-name α) →
    ValueTraceAgreement world-agreement [] F f →
    instantiateValue W α F n ≡ blamed Z →
    BlameTrace world-agreement (f N.•) Z

  coerce-blame-soundᵢ :
    ∀ n {W prefix θ τ V v Z}
      (world-agreement : WorldTraceAgreement W prefix) →
    TypeEnvironmentTraceAgreement world-agreement [] θ τ →
    ValueTraceAgreement world-agreement [] V v →
    ∀ {c} →
    coerceValue W θ c V n ≡ blamed Z →
    BlameTrace world-agreement (v N.⟨ C.renameᶜ τ c ⟩) Z

  finish-nu-blameᵢ :
    ∀ n {W prefix W₁ U γ θ L A c τ PL F f χL}
      (world-agreement : WorldTraceAgreement W prefix) →
    TypeEnvironmentTraceAgreement world-agreement [] θ τ →
    (path-L : WorldTracePath W χL W₁) →
    ValueTraceAgreement
      (world-trace-agreement-++ world-agreement path-L) [] F f →
    PL —↠[ χL ] f →
    interpret W γ θ L n ≡ returned W₁ F →
    interpret W γ θ (N.ν A L c) (suc n) ≡ blamed U →
    BlameTrace world-agreement
      (N.ν (renameᵗ τ A) PL (C.renameᶜ (extᵗ τ) c)) U

  interpret-blame-soundᵢ zero world-agreement no-M M-agrees ()

  interpret-blame-soundᵢ (suc n) {γ = γ} {M = N.` x}
      world-agreement N.no•-` M-agrees result-eq
      with lookup γ x
  interpret-blame-soundᵢ (suc n) {M = N.` x}
      world-agreement N.no•-` M-agrees () | just V
  interpret-blame-soundᵢ (suc n) {M = N.` x}
      world-agreement N.no•-` M-agrees () | nothing

  interpret-blame-soundᵢ (suc n) world-agreement
      (N.no•-ƛ no-N) M-agrees ()

  interpret-blame-soundᵢ (suc n) {W = W} {γ = γ} {θ = θ}
      {M = L N.· M} world-agreement (N.no•-· no-L no-M)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      result-eq
      with interpret W γ θ L n in L-eq
  interpret-blame-soundᵢ (suc n) world-agreement
      (N.no•-· no-L no-M) M-agrees () | timed W₁
  interpret-blame-soundᵢ (suc n) world-agreement
      (N.no•-· no-L no-M)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      result-eq | blamed W₁ =
    blame-trace-start-eq reification
      (blame-trace-result-eq result-eq
        (propagate-application-left-blame
          (reified-term-no-bullet γ-agrees no-M)
          (interpret-blame-soundᵢ n world-agreement no-L
            (term-trace-agreement τ vs θ-agrees γ-agrees refl) L-eq)))
  interpret-blame-soundᵢ (suc n) world-agreement
      (N.no•-· no-L no-M) M-agrees () | failed W₁ e
  interpret-blame-soundᵢ (suc n) {W = W} {γ = γ} {θ = θ}
      {M = L N.· M} world-agreement (N.no•-· no-L no-M)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      result-eq | returned W₁ F
      with interpret W₁ γ θ M n in M-eq
  interpret-blame-soundᵢ (suc n) world-agreement
      (N.no•-· no-L no-M) M-agrees () | returned W₁ F | timed W₂
  interpret-blame-soundᵢ (suc n) world-agreement
      (N.no•-· no-L no-M)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      result-eq | returned W₁ F | blamed W₂
      with interpret-return-soundᵢ n world-agreement no-L
        (term-trace-agreement τ vs θ-agrees γ-agrees refl) L-eq
  interpret-blame-soundᵢ (suc n) world-agreement
      (N.no•-· no-L no-M)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      result-eq | returned W₁ F | blamed W₂
      | return-trace χL f path-L L-reduction F-agrees =
    blame-trace-start-eq reification
      (blame-trace-result-eq result-eq
        (continue-application-after-function-return-to-blame
          world-agreement path-L (reified-term-no-bullet γ-agrees no-M)
          L-reduction
          (propagate-application-right-blame F-agrees
            (interpret-blame-soundᵢ n agreement-L no-M
              (term-trace-path-empty world-agreement path-L
                (term-trace-agreement τ vs θ-agrees γ-agrees refl))
              M-eq))))
    where
    agreement-L = world-trace-agreement-++ world-agreement path-L
  interpret-blame-soundᵢ (suc n) world-agreement
      (N.no•-· no-L no-M) M-agrees ()
      | returned W₁ F | failed W₂ e
  interpret-blame-soundᵢ (suc n) {W = W} {γ = γ} {θ = θ}
      {M = L N.· M} world-agreement (N.no•-· no-L no-M)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      result-eq | returned W₁ F | returned W₂ U
      with interpret-return-soundᵢ n world-agreement no-L
        (term-trace-agreement τ vs θ-agrees γ-agrees refl) L-eq
  interpret-blame-soundᵢ (suc n) world-agreement
      (N.no•-· no-L no-M)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      result-eq | returned W₁ F | returned W₂ U
      | return-trace χL f path-L L-reduction F-agrees
      with interpret-return-soundᵢ n agreement-L no-M
        (term-trace-path-empty world-agreement path-L
          (term-trace-agreement τ vs θ-agrees γ-agrees refl)) M-eq
    where
    agreement-L = world-trace-agreement-++ world-agreement path-L
  interpret-blame-soundᵢ (suc n) world-agreement
      (N.no•-· no-L no-M)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      result-eq | returned W₁ F | returned W₂ U
      | return-trace χL f path-L L-reduction F-agrees
      | return-trace χM u path-M M-reduction U-agrees
      with apply-blame-soundᵢ n agreement-M F-after-M U-agrees result-eq
    where
    agreement-L = world-trace-agreement-++ world-agreement path-L
    agreement-M = world-trace-agreement-++ agreement-L path-M
    F-after-M = value-trace-path-empty agreement-L path-M F-agrees
  interpret-blame-soundᵢ (suc n) world-agreement
      (N.no•-· no-L no-M)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      result-eq | returned W₁ F | returned W₂ U
      | return-trace χL f path-L L-reduction F-agrees
      | return-trace χM u path-M M-reduction U-agrees | A-trace =
    blame-trace-start-eq reification
      (continue-application-after-function-return-to-blame
        world-agreement path-L (reified-term-no-bullet γ-agrees no-M)
        L-reduction
        (continue-application-after-argument-return-to-blame
          agreement-L path-M F-agrees M-reduction A-trace))
    where
    agreement-L = world-trace-agreement-++ world-agreement path-L

  interpret-blame-soundᵢ (suc n) {M = N.Λ V}
      world-agreement (N.no•-Λ no-V) M-agrees result-eq
      with syntacticValue? V
  interpret-blame-soundᵢ (suc n) {M = N.Λ V}
      world-agreement (N.no•-Λ no-V) M-agrees () | no not-value
  interpret-blame-soundᵢ (suc n) {γ = γ} {θ = θ} {M = N.Λ V}
      world-agreement (N.no•-Λ no-V) M-agrees result-eq | yes vV
      with closeTypeAbstractionBody vV γ θ
  interpret-blame-soundᵢ (suc n) {M = N.Λ V}
      world-agreement (N.no•-Λ no-V) M-agrees ()
      | yes vV | just U
  interpret-blame-soundᵢ (suc n) {M = N.Λ V}
      world-agreement (N.no•-Λ no-V) M-agrees ()
      | yes vV | nothing

  interpret-blame-soundᵢ (suc n) {W = W} {γ = γ} {θ = θ}
      {M = N.ν A L c} {U = U} world-agreement (N.no•-ν no-L)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      result-eq
      with interpret W γ θ L n in L-eq
  interpret-blame-soundᵢ (suc n) world-agreement
      (N.no•-ν no-L) M-agrees () | timed W₁
  interpret-blame-soundᵢ (suc n) world-agreement
      (N.no•-ν no-L)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      result-eq | blamed W₁ =
    blame-trace-start-eq reification
      (blame-trace-result-eq result-eq
        (propagate-nu-left-blame
          (interpret-blame-soundᵢ n world-agreement no-L
            (term-trace-agreement τ vs θ-agrees γ-agrees refl) L-eq)))
  interpret-blame-soundᵢ (suc n) world-agreement
      (N.no•-ν no-L) M-agrees () | failed W₁ e
  interpret-blame-soundᵢ (suc n) {W = W} {γ = γ} {θ = θ}
      {M = N.ν A L c} {U = U} world-agreement (N.no•-ν no-L)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      result-eq | returned W₁ F =
    blame-trace-start-eq reification nu-trace
    where
    L-trace = interpret-return-soundᵢ n world-agreement no-L
      (term-trace-agreement τ vs θ-agrees γ-agrees refl) L-eq

    full-result-eq :
      interpret W γ θ (N.ν A L c) (suc n) ≡ blamed U
    full-result-eq rewrite L-eq =
      result-eq

    nu-trace : BlameTrace world-agreement _ U
    nu-trace with L-trace
    nu-trace | return-trace χL f path-L L-reduction F-agrees =
      finish-nu-blameᵢ n world-agreement θ-agrees path-L F-agrees
        L-reduction L-eq full-result-eq

  interpret-blame-soundᵢ (suc n) world-agreement N.no•-$ M-agrees ()

  interpret-blame-soundᵢ (suc n) {W = W} {γ = γ} {θ = θ}
      {M = L N.⊕[ op ] M} world-agreement (N.no•-⊕ no-L no-M)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      result-eq
      with interpret W γ θ L n in L-eq
  interpret-blame-soundᵢ (suc n) world-agreement
      (N.no•-⊕ no-L no-M) M-agrees () | timed W₁
  interpret-blame-soundᵢ (suc n) world-agreement
      (N.no•-⊕ no-L no-M)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      result-eq | blamed W₁ =
    blame-trace-start-eq reification
      (blame-trace-result-eq result-eq
        (propagate-primitive-left-blame
          (reified-term-no-bullet γ-agrees no-M)
          (interpret-blame-soundᵢ n world-agreement no-L
            (term-trace-agreement τ vs θ-agrees γ-agrees refl) L-eq)))
  interpret-blame-soundᵢ (suc n) world-agreement
      (N.no•-⊕ no-L no-M) M-agrees () | failed W₁ e
  interpret-blame-soundᵢ (suc n) {W = W} {γ = γ} {θ = θ}
      {M = L N.⊕[ op ] M} world-agreement (N.no•-⊕ no-L no-M)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      result-eq | returned W₁ F
      with interpret W₁ γ θ M n in M-eq
  interpret-blame-soundᵢ (suc n) world-agreement
      (N.no•-⊕ no-L no-M) M-agrees () | returned W₁ F | timed W₂
  interpret-blame-soundᵢ (suc n) world-agreement
      (N.no•-⊕ no-L no-M)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      result-eq | returned W₁ F | blamed W₂
      with interpret-return-soundᵢ n world-agreement no-L
        (term-trace-agreement τ vs θ-agrees γ-agrees refl) L-eq
  interpret-blame-soundᵢ (suc n) world-agreement
      (N.no•-⊕ no-L no-M)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      result-eq | returned W₁ F | blamed W₂
      | return-trace χL f path-L L-reduction F-agrees =
    blame-trace-start-eq reification
      (blame-trace-result-eq result-eq
        (continue-primitive-after-left-return-to-blame
          world-agreement path-L (reified-term-no-bullet γ-agrees no-M)
          L-reduction
          (propagate-primitive-right-blame F-agrees
            (interpret-blame-soundᵢ n agreement-L no-M
              (term-trace-path-empty world-agreement path-L
                (term-trace-agreement τ vs θ-agrees γ-agrees refl))
              M-eq))))
    where
    agreement-L = world-trace-agreement-++ world-agreement path-L
  interpret-blame-soundᵢ (suc n) world-agreement
      (N.no•-⊕ no-L no-M) M-agrees ()
      | returned W₁ F | failed W₂ e
  interpret-blame-soundᵢ (suc n) {W = W} {γ = γ} {θ = θ}
      {M = L N.⊕[ op ] M} world-agreement (N.no•-⊕ no-L no-M)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      result-eq | returned W₁ F | returned W₂ U =
    Data.Empty.⊥-elim (apply-primitive-not-blamed result-eq)

  interpret-blame-soundᵢ (suc n) {W = W} {γ = γ} {θ = θ}
      {M = M N.⟨ c ⟩} world-agreement (N.no•-⟨⟩ no-M)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      result-eq
      with interpret W γ θ M n in M-eq
  interpret-blame-soundᵢ (suc n) world-agreement
      (N.no•-⟨⟩ no-M) M-agrees () | timed W₁
  interpret-blame-soundᵢ (suc n) world-agreement
      (N.no•-⟨⟩ no-M)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      result-eq | blamed W₁ =
    blame-trace-start-eq reification
      (blame-trace-result-eq result-eq
        (propagate-cast-blame
          (interpret-blame-soundᵢ n world-agreement no-M
            (term-trace-agreement τ vs θ-agrees γ-agrees refl) M-eq)))
  interpret-blame-soundᵢ (suc n) world-agreement
      (N.no•-⟨⟩ no-M) M-agrees () | failed W₁ e
  interpret-blame-soundᵢ (suc n) world-agreement
      (N.no•-⟨⟩ no-M)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      result-eq | returned W₁ V
      with interpret-return-soundᵢ n world-agreement no-M
        (term-trace-agreement τ vs θ-agrees γ-agrees refl) M-eq
  interpret-blame-soundᵢ (suc n) world-agreement
      (N.no•-⟨⟩ no-M)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      result-eq | returned W₁ V
      | return-trace χM v path-M M-reduction V-agrees
      with type-environment-trace-path world-agreement path-M θ-agrees
  interpret-blame-soundᵢ (suc n) world-agreement
      (N.no•-⟨⟩ no-M)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      result-eq | returned W₁ V
      | return-trace χM v path-M M-reduction V-agrees
      | path-agreement
      with coerce-blame-soundᵢ n agreement-M
        (final-agreement path-agreement) V-agrees result-eq
    where
    agreement-M = world-trace-agreement-++ world-agreement path-M
  interpret-blame-soundᵢ (suc n) world-agreement
      (N.no•-⟨⟩ no-M)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      result-eq | returned W₁ V
      | return-trace χM v path-M M-reduction V-agrees
      | path-agreement | C-trace =
    blame-trace-start-eq reification
      (continue-under-cast-to-blame world-agreement path-M M-reduction
        (blame-trace-start-eq
          (cong (λ d → v N.⟨ d ⟩)
            (sym (coercion-action path-agreement _))) C-trace))

  interpret-blame-soundᵢ (suc n) world-agreement N.no•-blame
      M-agrees refl =
    blame-trace-start-eq (TermTraceAgreement.term-reification M-agrees)
      blame-trace-refl

  apply-blame-soundᵢ zero world-agreement F-agrees U-agrees ()
  apply-blame-soundᵢ (suc n) world-agreement
      (closure-trace-agrees
        {M = M} {M′ = body} {γ = γ} {θ = θ} {τ = τ} {vs = vs}
        θ-agrees γ-agrees no-M reification no-body)
      U-agrees result-eq
      with interpret-blame-soundᵢ n world-agreement no-M
        (term-trace-agreement τ (_ ∷ vs) θ-agrees
          (environment-cons-trace-agrees U-agrees γ-agrees) refl)
        result-eq
  apply-blame-soundᵢ (suc n) world-agreement
      (closure-trace-agrees
        {M = M} {M′ = body} {γ = γ} {θ = θ} {τ = τ} {vs = vs}
        θ-agrees γ-agrees no-M reification no-body)
      U-agrees result-eq | body-trace =
    closure-application-from-body-blame
      {M = M} {body = body} {τ = τ} {vs = vs}
      reification U-agrees body-trace

  apply-blame-soundᵢ (suc n) world-agreement
      constant-trace-agrees U-agrees ()
  apply-blame-soundᵢ (suc n) world-agreement
      (tagged-trace-agrees θ-agrees F-agrees) U-agrees ()
  apply-blame-soundᵢ (suc n) world-agreement
      (sealed-trace-agrees name-eq F-agrees) U-agrees ()
  apply-blame-soundᵢ (suc n) world-agreement
      (type-abstraction-trace-agrees fresh graph θ-agrees γ-agrees
        no-raw reification vP no-P)
      U-agrees ()
  apply-blame-soundᵢ (suc n) world-agreement
      (forall-proxy-trace-agrees θ-agrees F-agrees) U-agrees ()
  apply-blame-soundᵢ (suc n) world-agreement
      (generalized-trace-agrees θ-agrees F-agrees) U-agrees ()

  apply-blame-soundᵢ (suc n) {W = W}
      {F = function-proxy p q θ V} {U = U} world-agreement
      (function-proxy-trace-agrees θ-agrees F-agrees)
      U-agrees result-eq
      with coerceValue W θ p U n in p-eq
  apply-blame-soundᵢ (suc n) world-agreement
      (function-proxy-trace-agrees θ-agrees F-agrees)
      U-agrees () | timed W₁
  apply-blame-soundᵢ (suc n) world-agreement
      (function-proxy-trace-agrees θ-agrees F-agrees)
      U-agrees result-eq | blamed W₁ =
    blame-trace-result-eq result-eq
      (prepend-pure-step-to-blame
        (β-↦ (value-trace-value F-agrees) (value-trace-value U-agrees))
        (propagate-cast-blame
          (propagate-application-right-blame F-agrees
            (coerce-blame-soundᵢ n world-agreement θ-agrees U-agrees
              p-eq))))
  apply-blame-soundᵢ (suc n) world-agreement
      (function-proxy-trace-agrees θ-agrees F-agrees)
      U-agrees () | failed W₁ e
  apply-blame-soundᵢ (suc n) {W = W}
      {F = function-proxy p q θ V} {U = U} world-agreement
      (function-proxy-trace-agrees θ-agrees F-agrees)
      U-agrees result-eq | returned W₁ U′
      with applyValue W₁ V U′ n in apply-eq
  apply-blame-soundᵢ (suc n) world-agreement
      (function-proxy-trace-agrees θ-agrees F-agrees)
      U-agrees () | returned W₁ U′ | timed W₂
  apply-blame-soundᵢ (suc n) world-agreement
      (function-proxy-trace-agrees θ-agrees F-agrees)
      U-agrees result-eq | returned W₁ U′ | blamed W₂
      with coerce-return-soundᵢ n world-agreement θ-agrees U-agrees p-eq
  apply-blame-soundᵢ (suc n) world-agreement
      (function-proxy-trace-agrees θ-agrees F-agrees)
      U-agrees result-eq | returned W₁ U′ | blamed W₂
      | return-trace χP u′ path-P P-reduction U′-agrees =
    blame-trace-result-eq result-eq
      (prepend-pure-step-to-blame
        (β-↦ (value-trace-value F-agrees) (value-trace-value U-agrees))
        (propagate-cast-blame
          (continue-application-after-argument-return-to-blame
            world-agreement path-P F-agrees P-reduction
            (apply-blame-soundᵢ n agreement-P F-after-P U′-agrees
              apply-eq))))
    where
    agreement-P = world-trace-agreement-++ world-agreement path-P
    F-after-P = value-trace-path-empty world-agreement path-P F-agrees
  apply-blame-soundᵢ (suc n) world-agreement
      (function-proxy-trace-agrees θ-agrees F-agrees)
      U-agrees () | returned W₁ U′ | failed W₂ e
  apply-blame-soundᵢ (suc n) {W = W}
      {F = function-proxy p q θ V} {U = U} world-agreement
      (function-proxy-trace-agrees θ-agrees F-agrees)
      U-agrees result-eq | returned W₁ U′ | returned W₂ V′
      with coerce-return-soundᵢ n world-agreement θ-agrees U-agrees p-eq
  apply-blame-soundᵢ (suc n) world-agreement
      (function-proxy-trace-agrees θ-agrees F-agrees)
      U-agrees result-eq | returned W₁ U′ | returned W₂ V′
      | return-trace χP u′ path-P P-reduction U′-agrees
      with apply-return-soundᵢ n agreement-P F-after-P U′-agrees apply-eq
    where
    agreement-P = world-trace-agreement-++ world-agreement path-P
    F-after-P = value-trace-path-empty world-agreement path-P F-agrees
  apply-blame-soundᵢ (suc n) world-agreement
      (function-proxy-trace-agrees θ-agrees F-agrees)
      U-agrees result-eq | returned W₁ U′ | returned W₂ V′
      | return-trace χP u′ path-P P-reduction U′-agrees
      | return-trace χA v′ path-A A-reduction V′-agrees
      with continue-application-after-argument-return
        world-agreement path-P F-agrees P-reduction
        (return-trace χA v′ path-A A-reduction V′-agrees)
  apply-blame-soundᵢ (suc n) world-agreement
      (function-proxy-trace-agrees θ-agrees F-agrees)
      U-agrees result-eq | returned W₁ U′ | returned W₂ V′
      | return-trace χP u′ path-P P-reduction U′-agrees
      | return-trace χA v′ path-A A-reduction V′-agrees
      | return-trace χPA v′′ path-PA PA-reduction V′′-agrees
      with type-environment-trace-path world-agreement path-PA θ-agrees
  apply-blame-soundᵢ (suc n) world-agreement
      (function-proxy-trace-agrees θ-agrees F-agrees)
      U-agrees result-eq | returned W₁ U′ | returned W₂ V′
      | return-trace χP u′ path-P P-reduction U′-agrees
      | return-trace χA v′ path-A A-reduction V′-agrees
      | return-trace χPA v′′ path-PA PA-reduction V′′-agrees
      | path-agreement
      with coerce-blame-soundᵢ n agreement-PA
        (final-agreement path-agreement) V′′-agrees result-eq
    where
    agreement-PA = world-trace-agreement-++ world-agreement path-PA
  apply-blame-soundᵢ (suc n) world-agreement
      (function-proxy-trace-agrees θ-agrees F-agrees)
      U-agrees result-eq | returned W₁ U′ | returned W₂ V′
      | return-trace χP u′ path-P P-reduction U′-agrees
      | return-trace χA v′ path-A A-reduction V′-agrees
      | return-trace χPA v′′ path-PA PA-reduction V′′-agrees
      | path-agreement | Q-trace =
    prepend-pure-step-to-blame
      (β-↦ (value-trace-value F-agrees) (value-trace-value U-agrees))
      (continue-under-cast-to-blame world-agreement path-PA PA-reduction
        (blame-trace-start-eq
          (cong (λ d → v′′ N.⟨ d ⟩)
            (sym (coercion-action path-agreement _))) Q-trace))

  instantiate-blame-soundᵢ zero world-agreement newest F-agrees ()
  instantiate-blame-soundᵢ (suc n) world-agreement newest
      (type-abstraction-trace-agrees fresh graph θ-agrees γ-agrees
        no-raw reification vP no-P) ()
  instantiate-blame-soundᵢ (suc n) {W = W} {α = α}
      {F = forall-proxy c θ V} world-agreement newest
      (forall-proxy-trace-agrees {c = c} θ-agrees F-agrees)
      result-eq
      with instantiateValue W α V n in inst-eq
  instantiate-blame-soundᵢ (suc n) world-agreement newest
      (forall-proxy-trace-agrees {c = c} θ-agrees F-agrees)
      () | timed W₁
  instantiate-blame-soundᵢ (suc n) world-agreement newest
      (forall-proxy-trace-agrees {c = c} θ-agrees F-agrees)
      result-eq | blamed W₁ =
    blame-trace-result-eq result-eq
      (prepend-pure-step-to-blame
        (β-∀• (value-trace-value F-agrees))
        (propagate-cast-blame
          (instantiate-blame-soundᵢ n world-agreement newest F-agrees
            inst-eq)))
  instantiate-blame-soundᵢ (suc n) world-agreement newest
      (forall-proxy-trace-agrees {c = c} θ-agrees F-agrees)
      () | failed W₁ e
  instantiate-blame-soundᵢ (suc n) world-agreement newest
      (forall-proxy-trace-agrees {c = c} θ-agrees F-agrees)
      result-eq | returned W₁ U
      with instantiate-return-soundᵢ n world-agreement newest F-agrees
        inst-eq
  instantiate-blame-soundᵢ (suc n) world-agreement newest
      (forall-proxy-trace-agrees {c = c} θ-agrees F-agrees)
      result-eq | returned W₁ U
      | return-trace χI u path-I I-reduction U-agrees
      with type-environment-trace-path world-agreement path-I
        (type-environment-instantiate-head newest θ-agrees)
  instantiate-blame-soundᵢ (suc n) world-agreement newest
      (forall-proxy-trace-agrees {c = c} θ-agrees F-agrees)
      result-eq | returned W₁ U
      | return-trace χI u path-I I-reduction U-agrees
      | path-agreement
      with coerce-blame-soundᵢ n agreement-I
        (final-agreement path-agreement) U-agrees result-eq
    where
    agreement-I = world-trace-agreement-++ world-agreement path-I
  instantiate-blame-soundᵢ (suc n) world-agreement newest
      (forall-proxy-trace-agrees {c = c} θ-agrees F-agrees)
      result-eq | returned W₁ U
      | return-trace χI u path-I I-reduction U-agrees
      | path-agreement | C-trace =
    prepend-pure-step-to-blame
      (β-∀• (value-trace-value F-agrees))
      (blame-trace-start-eq
        (cong (λ d → (N._• _) N.⟨ d ⟩)
          (open-extended-coercion _ c))
        (continue-under-cast-to-blame world-agreement path-I I-reduction
          (blame-trace-start-eq
            (cong (λ d → u N.⟨ d ⟩)
              (sym (coercion-action path-agreement c))) C-trace)))
  instantiate-blame-soundᵢ (suc n) world-agreement newest
      (generalized-trace-agrees {c = c} θ-agrees F-agrees) result-eq
      with coerce-blame-soundᵢ n world-agreement
        (type-environment-instantiate-head newest θ-agrees)
        F-agrees result-eq
  instantiate-blame-soundᵢ (suc n) world-agreement newest
      (generalized-trace-agrees {c = c} θ-agrees F-agrees) result-eq
      | C-trace =
    prepend-pure-step-to-blame
      (β-gen• (value-trace-value F-agrees))
      (blame-trace-start-eq
        (cong (λ d → _ N.⟨ d ⟩) (open-extended-coercion _ c))
        C-trace)
  instantiate-blame-soundᵢ (suc n) world-agreement newest
      (closure-trace-agrees θ-agrees γ-agrees no-raw reification no-body) ()
  instantiate-blame-soundᵢ (suc n) world-agreement newest
      constant-trace-agrees ()
  instantiate-blame-soundᵢ (suc n) world-agreement newest
      (tagged-trace-agrees θ-agrees F-agrees) ()
  instantiate-blame-soundᵢ (suc n) world-agreement newest
      (sealed-trace-agrees name-eq F-agrees) ()
  instantiate-blame-soundᵢ (suc n) world-agreement newest
      (function-proxy-trace-agrees θ-agrees F-agrees) ()

  coerce-blame-soundᵢ zero world-agreement θ-agrees V-agrees ()
  coerce-blame-soundᵢ (suc n) world-agreement θ-agrees V-agrees
      {c = C.id A} ()
  coerce-blame-soundᵢ (suc n) {W = W} {θ = θ} {V = V}
      world-agreement θ-agrees V-agrees
      {c = c C.︔ d} result-eq
      with coerceValue W θ c V n in c-eq
  coerce-blame-soundᵢ (suc n) world-agreement θ-agrees V-agrees
      {c = c C.︔ d} () | timed W₁
  coerce-blame-soundᵢ (suc n) world-agreement θ-agrees V-agrees
      {c = c C.︔ d} result-eq | blamed W₁ =
    blame-trace-result-eq result-eq
      (prepend-pure-step-to-blame (β-seq (value-trace-value V-agrees))
        (propagate-cast-blame
          (coerce-blame-soundᵢ n world-agreement θ-agrees V-agrees
            c-eq)))
  coerce-blame-soundᵢ (suc n) world-agreement θ-agrees V-agrees
      {c = c C.︔ d} () | failed W₁ e
  coerce-blame-soundᵢ (suc n) world-agreement θ-agrees V-agrees
      {c = c C.︔ d} result-eq | returned W₁ U
      with coerce-return-soundᵢ n world-agreement θ-agrees V-agrees c-eq
  coerce-blame-soundᵢ (suc n) world-agreement θ-agrees V-agrees
      {c = c C.︔ d} result-eq | returned W₁ U
      | return-trace χC u path-C C-reduction U-agrees
      with type-environment-trace-path world-agreement path-C θ-agrees
  coerce-blame-soundᵢ (suc n) world-agreement θ-agrees V-agrees
      {c = c C.︔ d} result-eq | returned W₁ U
      | return-trace χC u path-C C-reduction U-agrees
      | path-agreement
      with coerce-blame-soundᵢ n agreement-C
        (final-agreement path-agreement) U-agrees result-eq
    where
    agreement-C = world-trace-agreement-++ world-agreement path-C
  coerce-blame-soundᵢ (suc n) world-agreement θ-agrees V-agrees
      {c = c C.︔ d} result-eq | returned W₁ U
      | return-trace χC u path-C C-reduction U-agrees
      | path-agreement | D-trace =
    prepend-pure-step-to-blame (β-seq (value-trace-value V-agrees))
      (continue-under-cast-to-blame world-agreement path-C C-reduction
        (blame-trace-start-eq
          (cong (λ q → u N.⟨ q ⟩)
            (sym (coercion-action path-agreement d))) D-trace))

  coerce-blame-soundᵢ (suc n) world-agreement θ-agrees V-agrees
      {c = p C.↦ q} ()
  coerce-blame-soundᵢ (suc n) world-agreement θ-agrees V-agrees
      {c = C.`∀ c} ()
  coerce-blame-soundᵢ (suc n) {θ = θ} world-agreement θ-agrees V-agrees
      {c = G C.!} result-eq
      with ground? θ G
  coerce-blame-soundᵢ (suc n) world-agreement θ-agrees V-agrees
      {c = G C.!} () | no not-ground
  coerce-blame-soundᵢ (suc n) world-agreement θ-agrees V-agrees
      {c = G C.!} () | yes runtime-ground

  coerce-blame-soundᵢ (suc n) {θ = θ} world-agreement θ-agrees V-agrees
      {c = G C.？} result-eq
      with ground? θ G in ground-eq
  coerce-blame-soundᵢ (suc n) world-agreement θ-agrees V-agrees
      {c = G C.？} () | no not-ground
  coerce-blame-soundᵢ (suc n) {θ = θ} world-agreement θ-agrees V-agrees
      {c = G C.？} result-eq | yes runtime-ground
      with tagOf θ (runtime-ground-syntax runtime-ground) in expected-eq
  coerce-blame-soundᵢ (suc n) world-agreement θ-agrees V-agrees
      {c = G C.？} () | yes runtime-ground | nothing
  coerce-blame-soundᵢ (suc n) world-agreement θ-agrees
      (tagged-trace-agrees {G = H} {gG = gH} {θ = σ}
        σ-agrees U-agrees)
      {c = G C.？} result-eq | yes runtime-ground | just expected
      with tagOf σ gH in actual-eq
  coerce-blame-soundᵢ (suc n) world-agreement θ-agrees
      (tagged-trace-agrees σ-agrees U-agrees)
      {c = G C.？} () | yes runtime-ground | just expected | nothing
  coerce-blame-soundᵢ (suc n) world-agreement θ-agrees
      (tagged-trace-agrees {G = H} {gG = gH} {θ = σ}
        σ-agrees U-agrees)
      {c = G C.？} result-eq | yes runtime-ground | just expected
      | just actual
      with expected ≟Tag actual
  coerce-blame-soundᵢ (suc n) world-agreement θ-agrees
      (tagged-trace-agrees σ-agrees U-agrees)
      {c = G C.？} () | yes runtime-ground | just expected
      | just .expected | yes refl
  coerce-blame-soundᵢ (suc n) world-agreement θ-agrees
      (tagged-trace-agrees {G = H} {gG = gH} {θ = σ}
        σ-agrees U-agrees)
      {c = G C.？} result-eq | yes runtime-ground | just expected
      | just actual | no mismatch =
    blame-trace-result-eq result-eq
      (untag-blame-sound
        {runtime-ground = runtime-ground} {gH = gH}
        θ-agrees σ-agrees U-agrees
        expected-eq actual-eq mismatch)
  coerce-blame-soundᵢ (suc n) world-agreement θ-agrees
      (closure-trace-agrees θ′-agrees γ-agrees no-raw reification no-body)
      {c = G C.？} () | yes runtime-ground | just expected
  coerce-blame-soundᵢ (suc n) world-agreement θ-agrees
      constant-trace-agrees {c = G C.？} ()
      | yes runtime-ground | just expected
  coerce-blame-soundᵢ (suc n) world-agreement θ-agrees
      (sealed-trace-agrees name-eq U-agrees) {c = G C.？} ()
      | yes runtime-ground | just expected
  coerce-blame-soundᵢ (suc n) world-agreement θ-agrees
      (function-proxy-trace-agrees θ′-agrees U-agrees)
      {c = G C.？} () | yes runtime-ground | just expected
  coerce-blame-soundᵢ (suc n) world-agreement θ-agrees
      (type-abstraction-trace-agrees fresh graph θ′-agrees γ-agrees
        no-raw reification vP no-P)
      {c = G C.？} () | yes runtime-ground | just expected
  coerce-blame-soundᵢ (suc n) world-agreement θ-agrees
      (forall-proxy-trace-agrees θ′-agrees U-agrees)
      {c = G C.？} () | yes runtime-ground | just expected
  coerce-blame-soundᵢ (suc n) world-agreement θ-agrees
      (generalized-trace-agrees θ′-agrees U-agrees)
      {c = G C.？} () | yes runtime-ground | just expected

  coerce-blame-soundᵢ (suc n) {θ = θ} world-agreement θ-agrees V-agrees
      {c = C.seal A X} result-eq
      with lookup θ X
  coerce-blame-soundᵢ (suc n) world-agreement θ-agrees V-agrees
      {c = C.seal A X} () | just (seal-name α)
  coerce-blame-soundᵢ (suc n) world-agreement θ-agrees V-agrees
      {c = C.seal A X} () | just (abstract-name Y)
  coerce-blame-soundᵢ (suc n) world-agreement θ-agrees V-agrees
      {c = C.seal A X} () | nothing

  coerce-blame-soundᵢ (suc n) {θ = θ} world-agreement θ-agrees V-agrees
      {c = C.unseal X A} result-eq
      with lookup θ X
  coerce-blame-soundᵢ (suc n) world-agreement θ-agrees V-agrees
      {c = C.unseal X A} () | nothing
  coerce-blame-soundᵢ (suc n) world-agreement θ-agrees V-agrees
      {c = C.unseal X A} () | just (abstract-name Y)
  coerce-blame-soundᵢ (suc n) world-agreement θ-agrees
      (sealed-trace-agrees {α = β} name-eq U-agrees)
      {c = C.unseal X A} result-eq | just (seal-name α)
      with α ≟SealName β
  coerce-blame-soundᵢ (suc n) world-agreement θ-agrees
      (sealed-trace-agrees name-eq U-agrees)
      {c = C.unseal X A} () | just (seal-name α) | yes refl
  coerce-blame-soundᵢ (suc n) world-agreement θ-agrees
      (sealed-trace-agrees name-eq U-agrees)
      {c = C.unseal X A} () | just (seal-name α) | no mismatch
  coerce-blame-soundᵢ (suc n) world-agreement θ-agrees
      (closure-trace-agrees θ′-agrees γ-agrees no-raw reification no-body)
      {c = C.unseal X A} () | just (seal-name α)
  coerce-blame-soundᵢ (suc n) world-agreement θ-agrees
      constant-trace-agrees {c = C.unseal X A} () | just (seal-name α)
  coerce-blame-soundᵢ (suc n) world-agreement θ-agrees
      (tagged-trace-agrees θ′-agrees U-agrees)
      {c = C.unseal X A} () | just (seal-name α)
  coerce-blame-soundᵢ (suc n) world-agreement θ-agrees
      (function-proxy-trace-agrees θ′-agrees U-agrees)
      {c = C.unseal X A} () | just (seal-name α)
  coerce-blame-soundᵢ (suc n) world-agreement θ-agrees
      (type-abstraction-trace-agrees fresh graph θ′-agrees γ-agrees
        no-raw reification vP no-P)
      {c = C.unseal X A} () | just (seal-name α)
  coerce-blame-soundᵢ (suc n) world-agreement θ-agrees
      (forall-proxy-trace-agrees θ′-agrees U-agrees)
      {c = C.unseal X A} () | just (seal-name α)
  coerce-blame-soundᵢ (suc n) world-agreement θ-agrees
      (generalized-trace-agrees θ′-agrees U-agrees)
      {c = C.unseal X A} () | just (seal-name α)
  coerce-blame-soundᵢ (suc n) world-agreement θ-agrees V-agrees
      {c = C.gen A c} ()

  coerce-blame-soundᵢ (suc n)
      {W = world next cells} {θ = θ} {τ = τ} {V = V} {v = v}
      world-agreement θ-agrees V-agrees
      {c = C.inst B c} result-eq
      with instantiateValue
        (allocate (world next cells) ★ θ) (seal-name-id next) V n
        in inst-eq
  coerce-blame-soundᵢ (suc n)
      {W = world next cells} {θ = θ} {τ = τ} {V = V} {v = v}
      world-agreement θ-agrees V-agrees
      {c = C.inst B c} () | timed W₃
  coerce-blame-soundᵢ (suc n)
      {W = world next cells} {θ = θ} {τ = τ} {V = V} {v = v}
      world-agreement θ-agrees V-agrees
      {c = C.inst B c} result-eq | blamed W₃
      with instantiate-blame-soundᵢ n agreement-B newest-lookup
        V-after-bind inst-eq
    where
    path-B = allocation-path {A = ★} world-agreement θ-agrees
    agreement-B = world-trace-agreement-++ world-agreement path-B
    V-after-bind = value-trace-path-empty world-agreement path-B V-agrees
    newest-lookup = new-seal-lookup []
      {next = next} {cells = cells} {A = ★} {θ = θ}
  coerce-blame-soundᵢ (suc n)
      {W = world next cells} {θ = θ} {τ = τ} {V = V} {v = v}
      world-agreement θ-agrees V-agrees
      {c = C.inst B c} result-eq | blamed W₃
      | blame-trace χI path-I I-reduction =
    blame-trace-result-eq result-eq
      (prepend-pure-step-to-blame (β-inst (value-trace-value V-agrees))
        (blame-trace (bind ★ ∷ (χI ++ keep ∷ []))
          (world-trace-path-++ path-B
            (world-trace-path-++ path-I
              (world-trace-keep world-trace-done)))
          (↠-step
            (ν-step (value-trace-value V-agrees)
              (value-trace-no-bullet V-agrees))
            (↠-trans (cast-↠ I-reduction)
              (↠-step (pure-step NuReduction.blame-⟨⟩) ↠-refl)))))
    where
    path-B = allocation-path {A = ★} world-agreement θ-agrees
  coerce-blame-soundᵢ (suc n)
      {W = world next cells} {θ = θ} {τ = τ} {V = V} {v = v}
      world-agreement θ-agrees V-agrees
      {c = C.inst B c} () | failed W₃ e
  coerce-blame-soundᵢ (suc n)
      {W = world next cells} {θ = θ} {τ = τ} {V = V} {v = v}
      world-agreement θ-agrees V-agrees
      {c = C.inst B c} result-eq | returned W₃ U
      with coerceValue W₃ (seal-name (seal-name-id next) ∷ θ) c U n
        in coerce-eq
  coerce-blame-soundᵢ (suc n)
      {W = world next cells} {θ = θ} {τ = τ} {V = V} {v = v}
      world-agreement θ-agrees V-agrees
      {c = C.inst B c} () | returned W₃ U | timed W₄
  coerce-blame-soundᵢ (suc n)
      {W = world next cells} {θ = θ} {τ = τ} {V = V} {v = v}
      world-agreement θ-agrees V-agrees
      {c = C.inst B c} result-eq | returned W₃ U | blamed W₄
      with instantiate-return-soundᵢ n agreement-B newest-lookup
        V-after-bind inst-eq
    where
    path-B = allocation-path {A = ★} world-agreement θ-agrees
    agreement-B = world-trace-agreement-++ world-agreement path-B
    V-after-bind = value-trace-path-empty world-agreement path-B V-agrees
    newest-lookup = new-seal-lookup []
      {next = next} {cells = cells} {A = ★} {θ = θ}
  coerce-blame-soundᵢ (suc n)
      {W = world next cells} {θ = θ} {τ = τ} {V = V} {v = v}
      world-agreement θ-agrees V-agrees
      {c = C.inst B c} result-eq | returned W₃ U | blamed W₄
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
  coerce-blame-soundᵢ (suc n)
      {W = world next cells} {θ = θ} {τ = τ} {V = V} {v = v}
      world-agreement θ-agrees V-agrees
      {c = C.inst B c} result-eq | returned W₃ U | blamed W₄
      | return-trace χI u path-I I-reduction U-agrees
      | path-agreement-I
      with coerce-blame-soundᵢ n agreement-I
        (final-agreement path-agreement-I) U-agrees coerce-eq
    where
    path-B = allocation-path {A = ★} world-agreement θ-agrees
    agreement-B = world-trace-agreement-++ world-agreement path-B
    agreement-I = world-trace-agreement-++ agreement-B path-I
  coerce-blame-soundᵢ (suc n)
      {W = world next cells} {θ = θ} {τ = τ} {V = V} {v = v}
      world-agreement θ-agrees V-agrees
      {c = C.inst B c} result-eq | returned W₃ U | blamed W₄
      | return-trace χI u path-I I-reduction U-agrees
      | path-agreement-I | C-trace
      with continue-under-cast-to-blame agreement-B path-I I-reduction
        (blame-trace-start-eq c-start-eq C-trace)
    where
    path-B = allocation-path {A = ★} world-agreement θ-agrees
    agreement-B = world-trace-agreement-++ world-agreement path-B
    c-start-eq = cong (λ d → u N.⟨ d ⟩)
      (sym
        (trans (coercion-action path-agreement-I c)
          (cong (applyCoercions χI)
            (renameᶜ-cong (extend-after-insertion τ) c))))
  coerce-blame-soundᵢ (suc n)
      {W = world next cells} {θ = θ} {τ = τ} {V = V} {v = v}
      world-agreement θ-agrees V-agrees
      {c = C.inst B c} result-eq | returned W₃ U | blamed W₄
      | return-trace χI u path-I I-reduction U-agrees
      | path-agreement-I | C-trace
      | blame-trace χR path-R R-reduction =
    blame-trace-result-eq result-eq
      (prepend-pure-step-to-blame (β-inst (value-trace-value V-agrees))
        (blame-trace (bind ★ ∷ χR)
          (world-trace-path-++ path-B path-R)
          (↠-step
            (ν-step (value-trace-value V-agrees)
              (value-trace-no-bullet V-agrees)) R-reduction)))
    where
    path-B = allocation-path {A = ★} world-agreement θ-agrees
  coerce-blame-soundᵢ (suc n)
      {W = world next cells} {θ = θ} {τ = τ} {V = V} {v = v}
      world-agreement θ-agrees V-agrees
      {c = C.inst B c} () | returned W₃ U | failed W₄ e

  finish-nu-blameᵢ n
      {W₁ = world next cells} {θ = θ} {A = A} {c = c}
      {τ = τ} {F = F} {f = f} {χL = χL}
      world-agreement θ-agrees path-L F-agrees L-reduction
      L-eq result-eq
      rewrite L-eq
      with instantiateValue W₂ α F n in inst-eq
    where
    α = seal-name-id next
    W₂ = allocate (world next cells) A θ
  finish-nu-blameᵢ n
      {W₁ = world next cells} {θ = θ} {A = A} {c = c}
      {τ = τ} {F = F} {f = f} {χL = χL}
      world-agreement θ-agrees path-L F-agrees L-reduction
      L-eq () | timed W₃
  finish-nu-blameᵢ n
      {W₁ = world next cells} {θ = θ} {A = A} {c = c}
      {τ = τ} {F = F} {f = f} {χL = χL}
      world-agreement θ-agrees path-L F-agrees L-reduction
      L-eq result-eq | blamed W₃
      with type-environment-trace-path world-agreement path-L θ-agrees
  finish-nu-blameᵢ n
      {W₁ = world next cells} {θ = θ} {A = A} {c = c}
      {τ = τ} {F = F} {f = f} {χL = χL}
      world-agreement θ-agrees path-L F-agrees L-reduction
      L-eq result-eq | blamed W₃ | path-agreement-L
      with instantiate-blame-soundᵢ n agreement-B newest-lookup
        F-after-bind inst-eq
    where
    agreement-L = world-trace-agreement-++ world-agreement path-L
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
  finish-nu-blameᵢ n
      {W₁ = world next cells} {θ = θ} {A = A} {c = c}
      {τ = τ} {F = F} {f = f} {χL = χL}
      world-agreement θ-agrees path-L F-agrees L-reduction
      L-eq result-eq | blamed W₃ | path-agreement-L | I-trace
      with propagate-cast-blame {c = c₁} I-trace
    where
    agreement-L = world-trace-agreement-++ world-agreement path-L
    c₁ = applyCoercionUnderTyBinders χL (C.renameᶜ (extᵗ τ) c)
  finish-nu-blameᵢ n
      {W₁ = world next cells} {θ = θ} {A = A} {c = c}
      {τ = τ} {F = F} {f = f} {χL = χL}
      world-agreement θ-agrees path-L F-agrees L-reduction
      L-eq result-eq | blamed W₃ | path-agreement-L | I-trace
      | blame-trace χR path-R R-reduction =
    blame-trace-result-eq result-eq
      (blame-trace (χL ++ (bind A₁ ∷ χR))
        (world-trace-path-++ path-L
          (world-trace-path-++ path-B path-R))
        (↠-trans (ν-↠ L-reduction)
          (↠-step
            (ν-step (value-trace-value F-agrees)
              (value-trace-no-bullet F-agrees)) R-reduction)))
    where
    agreement-L = world-trace-agreement-++ world-agreement path-L
    A₁ = applyTys χL (renameᵗ τ A)
    canonical-bind = allocation-path {A = A} agreement-L
      (final-agreement path-agreement-L)
    path-B = subst
      (λ B → WorldTracePath (world next cells) (bind B ∷ [])
        (allocate (world next cells) A θ))
      (type-action path-agreement-L A) canonical-bind
  finish-nu-blameᵢ n
      {W₁ = world next cells} {θ = θ} {A = A} {c = c}
      {τ = τ} {F = F} {f = f} {χL = χL}
      world-agreement θ-agrees path-L F-agrees L-reduction
      L-eq () | failed W₃ e
  finish-nu-blameᵢ n
      {W₁ = world next cells} {θ = θ} {A = A} {c = c}
      {τ = τ} {F = F} {f = f} {χL = χL}
      world-agreement θ-agrees path-L F-agrees L-reduction
      L-eq result-eq | returned W₃ U
      with coerceValue W₃ (seal-name (seal-name-id next) ∷ θ) c U n
        in coerce-eq
  finish-nu-blameᵢ n
      {W₁ = world next cells} {θ = θ} {A = A} {c = c}
      {τ = τ} {F = F} {f = f} {χL = χL}
      world-agreement θ-agrees path-L F-agrees L-reduction
      L-eq () | returned W₃ U | timed W₄
  finish-nu-blameᵢ n
      {W₁ = world next cells} {θ = θ} {A = A} {c = c}
      {τ = τ} {F = F} {f = f} {χL = χL}
      world-agreement θ-agrees path-L F-agrees L-reduction
      L-eq result-eq | returned W₃ U | blamed W₄
      with type-environment-trace-path world-agreement path-L θ-agrees
  finish-nu-blameᵢ n
      {W₁ = world next cells} {θ = θ} {A = A} {c = c}
      {τ = τ} {F = F} {f = f} {χL = χL}
      world-agreement θ-agrees path-L F-agrees L-reduction
      L-eq result-eq | returned W₃ U | blamed W₄
      | path-agreement-L
      with instantiate-return-soundᵢ n agreement-B newest-lookup
        F-after-bind inst-eq
    where
    agreement-L = world-trace-agreement-++ world-agreement path-L
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
  finish-nu-blameᵢ n
      {W₁ = world next cells} {θ = θ} {A = A} {c = c}
      {τ = τ} {F = F} {f = f} {χL = χL}
      world-agreement θ-agrees path-L F-agrees L-reduction
      L-eq result-eq | returned W₃ U | blamed W₄
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
  finish-nu-blameᵢ n
      {W₁ = world next cells} {θ = θ} {A = A} {c = c}
      {τ = τ} {F = F} {f = f} {χL = χL}
      world-agreement θ-agrees path-L F-agrees L-reduction
      L-eq result-eq | returned W₃ U | blamed W₄
      | path-agreement-L
      | return-trace χI u path-I I-reduction U-agrees
      | path-agreement-I
      with coerce-blame-soundᵢ n agreement-I
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
  finish-nu-blameᵢ n
      {W₁ = world next cells} {θ = θ} {A = A} {c = c}
      {τ = τ} {PL = PL} {F = F} {f = f} {χL = χL}
      world-agreement θ-agrees path-L F-agrees L-reduction
      L-eq result-eq | returned W₃ U | blamed W₄
      | path-agreement-L
      | return-trace χI u path-I I-reduction U-agrees
      | path-agreement-I | C-trace
      with continue-under-cast-to-blame agreement-B path-I I-reduction
        (blame-trace-start-eq c-start-eq C-trace)
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
  finish-nu-blameᵢ n
      {W₁ = world next cells} {θ = θ} {A = A} {c = c}
      {τ = τ} {PL = PL} {F = F} {f = f} {χL = χL}
      world-agreement θ-agrees path-L F-agrees L-reduction
      L-eq result-eq | returned W₃ U | blamed W₄
      | path-agreement-L
      | return-trace χI u path-I I-reduction U-agrees
      | path-agreement-I | C-trace
      | blame-trace χR path-R R-reduction =
    blame-trace-result-eq result-eq
      (blame-trace (χL ++ (bind A₁ ∷ χR))
        (world-trace-path-++ path-L
          (world-trace-path-++ path-B path-R))
        (↠-trans (ν-↠ L-reduction)
          (↠-step
            (ν-step (value-trace-value F-agrees)
              (value-trace-no-bullet F-agrees)) R-reduction)))
    where
    agreement-L = world-trace-agreement-++ world-agreement path-L
    A₁ = applyTys χL (renameᵗ τ A)
    canonical-bind = allocation-path {A = A} agreement-L
      (final-agreement path-agreement-L)
    path-B = subst
      (λ B → WorldTracePath (world next cells) (bind B ∷ [])
        (allocate (world next cells) A θ))
      (type-action path-agreement-L A) canonical-bind
  finish-nu-blameᵢ n
      {W₁ = world next cells} {θ = θ} {A = A} {c = c}
      {τ = τ} {F = F} {f = f} {χL = χL}
      world-agreement θ-agrees path-L F-agrees L-reduction
      L-eq () | returned W₃ U | failed W₄ e

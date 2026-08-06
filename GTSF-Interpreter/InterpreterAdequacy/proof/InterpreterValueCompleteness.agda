module InterpreterAdequacy.proof.InterpreterValueCompleteness where

-- File Charter:
--   * Proves completeness when the reified interpreter configuration is
--     already an official syntactic value.
--   * Handles environment lookup and inert coercion frames explicitly, so
--     the raw interpreter term itself need not be a syntactic value.
--   * Constructs no small-step reduction and assumes no normalization result.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([])
open import Data.Maybe using (just)
open import Data.Nat using (suc; zero)
open import Data.Nat.Properties using (+-identityʳ; +-suc)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)
open import Relation.Nullary using (yes)

import Coercions as C
open import Coercions using (_∣_∣_⊢_∶_=⇒_)
open import Interpreter
open import InterpreterAdequacy.TraceAgreement
open import InterpreterAdequacy.proof.ClosedValueTrace using
  (closed-value-trace)
open import InterpreterAdequacy.proof.InterpreterTermNoBullet using
  (interpreter-term-no-bullet)
open import InterpreterAdequacy.proof.SmallStepReturnCompletenessBase using
  (closed-value-eventually-returns)
open import InterpreterAdequacy.proof.SyntaxReification using
  (lookup-environment-trace; reified-term)
open import Runtime.InterpreterClosedValueFrame
open import Core.InterpreterFuel using (interpret-terminal-stable)
open import Runtime.InterpreterInertFrameCore
open import Core.InterpreterOutcome using (terminal-return)
open import Typing.InterpreterSemanticTypingCore
open import SmallStepInterface.InterpreterTermShape
import NuTerms as N
open import proof.InterpreterClosedValueProof using (closeValue-closed)
open import proof.InterpreterCloseValueTyping using (closeValue-defined)
open import proof.InterpreterSyntacticValueComputationProof using
  (interpret-cast-computation)
open import proof.InterpreterSemanticTypingProperties using
  (environment-lookup-sound; store-lookup-sound)
open import proof.InterpreterCoercionTyping using
  (ground?-complete; runtime-ground-from-typing)
open import Types

rename-inert-reflect :
  ∀ ρ {c} →
  C.Inert (C.renameᶜ ρ c) →
  C.Inert c
rename-inert-reflect ρ {C.id A} ()
rename-inert-reflect ρ {c C.︔ d} ()
rename-inert-reflect ρ {c C.↦ d} inert = c C.↦ d
rename-inert-reflect ρ {C.`∀ c} inert = C.`∀ c
rename-inert-reflect ρ {G C.!} inert = G C.!
rename-inert-reflect ρ {G C.？} ()
rename-inert-reflect ρ {C.seal A X} inert = C.seal A X
rename-inert-reflect ρ {C.unseal X A} ()
rename-inert-reflect ρ {C.gen A c} inert = C.gen A c
rename-inert-reflect ρ {C.inst B c} ()

execute-inert-frame-local :
  ∀ {W Δ Σ θ μ c A B V}
    (runtime : RuntimeContext W Δ Σ θ)
    (runtime-env : RuntimeTypeEnvironment θ)
    (typing : μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B)
    (inert : C.Inert c) →
  InertFrameExecution W θ c V inert
execute-inert-frame-local {W = W} {θ = θ} {V = V}
    runtime runtime-env
    (C.cast-tag hG gG allowed) (G C.!)
    with ground?-complete
      (runtime-ground-from-typing runtime-env runtime hG gG)
execute-inert-frame-local {W = W} {θ = θ} {V = V}
    runtime runtime-env
    (C.cast-tag hG gG allowed) (G C.!)
    | runtime-ground , ground-eq =
  inert-frame-execution
    (tagged (runtime-ground-syntax runtime-ground) _ _)
    closed-tag-frame
    (λ n → tag-computes
      {W = W} {θ = θ} {G = G} {V = V} {n = n}
      {runtime-ground = runtime-ground} ground-eq)
  where
  tag-computes : ∀ {W θ G V n runtime-ground}
    → ground? θ G ≡ yes runtime-ground
    → coerceValue W θ (G C.!) V (suc n) ≡
      returned W (tagged (runtime-ground-syntax runtime-ground) θ V)
  tag-computes ground-eq rewrite ground-eq = refl
execute-inert-frame-local {W = W} {θ = θ} {V = V}
    runtime runtime-env
    (C.cast-seal hA X∈Σ allowed) (C.seal A X)
    with store-lookup-sound
      (Typing.InterpreterSemanticTypingCore.store-typing runtime) X∈Σ
execute-inert-frame-local {W = W} {θ = θ} {V = V}
    runtime runtime-env
    (C.cast-seal hA X∈Σ allowed) (C.seal A X)
    | α , lookup-eq , representation =
  inert-frame-execution (sealed α V)
    (closed-seal-frame lookup-eq)
    (λ n → seal-computes
      {W = W} {θ = θ} {A = A} {X = X} {V = V}
      {n = n} {α = α} lookup-eq)
  where
  seal-computes :
    ∀ {W θ A X V n α} →
    lookup θ X ≡ just (seal-name α) →
    coerceValue W θ (C.seal A X) V (suc n) ≡
      returned W (sealed α V)
  seal-computes lookup-eq rewrite lookup-eq = refl
execute-inert-frame-local runtime runtime-env
    (C.cast-fun p⊢ q⊢) (p C.↦ q) =
  inert-frame-execution (function-proxy p q _ _)
    closed-function-frame (λ n → refl)
execute-inert-frame-local runtime runtime-env
    (C.cast-all c⊢) (C.`∀ c) =
  inert-frame-execution (forall-proxy c _ _)
    closed-forall-frame (λ n → refl)
execute-inert-frame-local runtime runtime-env
    (C.cast-gen hA occ c⊢) (C.gen A c) =
  inert-frame-execution (generalized A c _ _)
    closed-generalized-frame (λ n → refl)

frame-trace-agreement :
  ∀ {W prefix}
    {world-agreement : WorldTraceAgreement W prefix}
    {θ τ c V U v}
    {inert : C.Inert c} →
  TypeEnvironmentTraceAgreement world-agreement [] θ τ →
  ClosedValueFrame θ V inert U →
  ValueTraceAgreement world-agreement [] V v →
  ValueTraceAgreement world-agreement [] U
    (v N.⟨ C.renameᶜ τ c ⟩)
frame-trace-agreement θ-agrees closed-tag-frame V-agrees =
  tagged-trace-agrees θ-agrees V-agrees
frame-trace-agreement θ-agrees
    (closed-seal-frame name-eq) V-agrees =
  sealed-trace-agrees
    (TypeEnvironmentTraceAgreement.type-trace-lookup-agrees
      θ-agrees name-eq)
    V-agrees
frame-trace-agreement θ-agrees closed-function-frame V-agrees =
  function-proxy-trace-agrees θ-agrees V-agrees
frame-trace-agreement θ-agrees closed-forall-frame V-agrees =
  forall-proxy-trace-agrees θ-agrees V-agrees
frame-trace-agreement θ-agrees closed-generalized-frame V-agrees =
  generalized-trace-agrees θ-agrees V-agrees

interpret-return-next :
  ∀ {W γ θ M V n} →
  interpret W γ θ M n ≡ returned W V →
  interpret W γ θ M (suc n) ≡ returned W V
interpret-return-next {W} {γ} {θ} {M} {V} {n} result-eq =
  subst
    (λ index → interpret W γ θ M index ≡ returned W V)
    (trans (+-suc n zero) (cong suc (+-identityʳ n)))
    (interpret-terminal-stable
      {W = W} {γ = γ} {θ = θ} {M = M}
      {n = n} {o = returned W V}
      terminal-return result-eq (suc zero))

application-not-value : ∀ {L M} → N.Value (L N.· M) → ⊥
application-not-value ()

nu-not-value : ∀ {A L c} → N.Value (N.ν A L c) → ⊥
nu-not-value ()

primitive-not-value : ∀ {L op M} → N.Value (L N.⊕[ op ] M) → ⊥
primitive-not-value ()

mutual
  interpret-value-completeᵢ :
    ∀ {W prefix Δ Σ Γ γ θ M P A}
      (world-agreement : WorldTraceAgreement W prefix) →
    RuntimeContext W Δ Σ θ →
    RuntimeTypeEnvironment θ →
    EnvironmentTyping W θ γ Γ →
    (image : InterpreterTerm M) →
    N._∣_∣_⊢_⦂_ Δ Σ Γ M A →
    TermTraceAgreement world-agreement [] γ θ M P →
    N.Value P →
    Σ[ n ∈ StepIndex ]
    Σ[ V ∈ Value ]
      (interpret W γ θ M n ≡ returned W V) ×
      ValueTraceAgreement world-agreement [] V P

  interpret-value-completeᵢ {W = W} {γ = γ} {θ = θ}
      world-agreement runtime runtime-env γ⊢
      (variable-term x) (N.⊢` x∈)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      vP
      with environment-lookup-sound γ⊢ x∈
  interpret-value-completeᵢ {W = W} {γ = γ} {θ = θ}
      world-agreement runtime runtime-env γ⊢
      (variable-term x) (N.⊢` x∈)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      vP
      | V , lookup-eq , V⊢
      with lookup-environment-trace γ-agrees lookup-eq
  interpret-value-completeᵢ {W = W} {γ = γ} {θ = θ}
      world-agreement runtime runtime-env γ⊢
      (variable-term x) (N.⊢` x∈)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      vP
      | V , lookup-eq , V⊢ | v , env-eq , V-agrees =
    suc zero , V , variable-return ,
      subst (ValueTraceAgreement world-agreement [] V)
        (sym (trans reification env-eq)) V-agrees
    where
    variable-return :
      interpret W γ θ (N.` x) (suc zero) ≡ returned W V
    variable-return rewrite lookup-eq = refl

  interpret-value-completeᵢ world-agreement runtime runtime-env γ⊢
      image@(closure-term M-ok) M⊢
      agreement@(term-trace-agreement τ vs θ-agrees γ-agrees reification)
      vP =
    close-immediate world-agreement runtime runtime-env γ⊢
      image M⊢ agreement (N.ƛ _) vP

  interpret-value-completeᵢ world-agreement runtime runtime-env γ⊢
      (application-term L-ok M-ok) (N.⊢· L⊢ M⊢)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      vP
      rewrite reification =
    ⊥-elim (application-not-value vP)

  interpret-value-completeᵢ world-agreement runtime runtime-env γ⊢
      image@(type-abstraction-term vV V-ok) M⊢
      agreement@(term-trace-agreement τ vs θ-agrees γ-agrees reification)
      vP =
    close-immediate world-agreement runtime runtime-env γ⊢
      image M⊢ agreement (N.Λ vV) vP

  interpret-value-completeᵢ world-agreement runtime runtime-env γ⊢
      (instantiation-term L-ok) (N.⊢ν hA L⊢ c⊢)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      vP
      rewrite reification =
    ⊥-elim (nu-not-value vP)

  interpret-value-completeᵢ world-agreement runtime runtime-env γ⊢
      image@(constant-term κ) M⊢
      agreement@(term-trace-agreement τ vs θ-agrees γ-agrees reification)
      vP =
    close-immediate world-agreement runtime runtime-env γ⊢
      image M⊢ agreement (N.$ κ) vP

  interpret-value-completeᵢ world-agreement runtime runtime-env γ⊢
      (primitive-term op L-ok M-ok) (N.⊢⊕ L⊢ .op M⊢)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      vP
      rewrite reification =
    ⊥-elim (primitive-not-value vP)

  interpret-value-completeᵢ {W = W} {γ = γ} {θ = θ}
      {M = M N.⟨ c ⟩}
      world-agreement runtime runtime-env γ⊢
      (coercion-application-term M-ok) (N.⊢⟨⟩ c⊢ M⊢)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      vP
      rewrite reification
      with vP
  interpret-value-completeᵢ {W = W} {γ = γ} {θ = θ}
      {M = M N.⟨ c ⟩}
      world-agreement runtime runtime-env γ⊢
      (coercion-application-term M-ok) (N.⊢⟨⟩ c⊢ M⊢)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      vP
      | vQ N.⟨ inert ⟩
      with interpret-value-completeᵢ world-agreement runtime runtime-env γ⊢
        M-ok M⊢
        (term-trace-agreement τ vs θ-agrees γ-agrees refl) vQ
  interpret-value-completeᵢ {W = W} {γ = γ} {θ = θ}
      {M = M N.⟨ c ⟩}
      world-agreement runtime runtime-env γ⊢
      (coercion-application-term M-ok) (N.⊢⟨⟩ c⊢ M⊢)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      vP
      | vQ N.⟨ inert ⟩ | n , V , body-return , V-agrees
      with execute-inert-frame-local runtime runtime-env c⊢
        (rename-inert-reflect τ inert)
  interpret-value-completeᵢ {W = W} {γ = γ} {θ = θ}
      {M = M N.⟨ c ⟩}
      world-agreement runtime runtime-env γ⊢
      (coercion-application-term M-ok) (N.⊢⟨⟩ c⊢ M⊢)
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      vP
      | vQ N.⟨ inert ⟩ | n , V , body-return , V-agrees
      | execution =
    suc (suc n) , Runtime.InterpreterInertFrameCore.result execution ,
      cast-return ,
      frame-trace-agreement θ-agrees
        (Runtime.InterpreterInertFrameCore.frame execution) V-agrees
    where
    cast-return :
      interpret W γ θ (M N.⟨ c ⟩) (suc (suc n)) ≡
        returned W (Runtime.InterpreterInertFrameCore.result execution)
    cast-return =
      trans
        (interpret-cast-computation
          {W = W} {γ = γ} {θ = θ} {M = M} {c = c}
          {n = suc n} {outcome = returned W V}
          (interpret-return-next
            {W = W} {γ = γ} {θ = θ} {M = M} {V = V} {n = n}
            body-return))
        (Runtime.InterpreterInertFrameCore.computes execution n)

  close-immediate :
    ∀ {W prefix Δ Σ Γ γ θ M P A}
      (world-agreement : WorldTraceAgreement W prefix) →
    RuntimeContext W Δ Σ θ →
    RuntimeTypeEnvironment θ →
    EnvironmentTyping W θ γ Γ →
    (image : InterpreterTerm M) →
    (M⊢ : N._∣_∣_⊢_⦂_ Δ Σ Γ M A) →
    (agreement : TermTraceAgreement world-agreement [] γ θ M P) →
    (vM : N.Value M) →
    N.Value P →
    Σ[ n ∈ StepIndex ]
    Σ[ V ∈ Value ]
      (interpret W γ θ M n ≡ returned W V) ×
      ValueTraceAgreement world-agreement [] V P
  close-immediate world-agreement runtime runtime-env γ⊢ image M⊢
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      vM vP
      with closeValue-defined runtime γ⊢ image vM M⊢
  close-immediate world-agreement runtime runtime-env γ⊢ image M⊢
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      vM vP | V , close-eq
      with closed-value-eventually-returns vM close-eq
  close-immediate world-agreement runtime runtime-env γ⊢ image M⊢
      (term-trace-agreement τ vs θ-agrees γ-agrees reification)
      vM vP | V , close-eq | n , result-eq =
    n , V , result-eq ,
      subst (ValueTraceAgreement world-agreement [] V)
        (sym reification)
        (closed-value-trace (closeValue-closed vM close-eq)
          θ-agrees γ-agrees (interpreter-term-no-bullet image))

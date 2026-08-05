module proof.InterpreterSyntacticValueTerminationProof where

-- File Charter:
--   * Proves that successfully closed, well-typed syntactic values return
--     their exact closed value at some finite interpreter index.
--   * Counts only direct interpreter calls and uses terminal fuel stability
--     to leave one positive index for an enclosing inert coercion.
--   * Contains no small-step reduction, catch-up result, or DGG theorem.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (suc)
open import Data.Nat.Properties using (+-identityʳ; +-suc)
open import Data.Product using (_,_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using
  (cong; subst; trans)
open import Relation.Nullary using (no; yes)

import Coercions as C
open import Interpreter
open import Core.InterpreterFuel using (interpret-terminal-stable)
open import Runtime.InterpreterInertFrame using
  (computes; execute-inert-frame; result)
open import Core.InterpreterOutcome using (terminal-return)
open import Typing.InterpreterSemanticTypingCore using (RuntimeContext)
open import Runtime.InterpreterSyntacticValueComputation using
  (syntactic-value-return-unique)
import NuTerms as N
open import proof.InterpreterCloseValueTyping using
  (syntacticValue-complete)
open import proof.InterpreterSyntacticValueComputationProof using
  ( interpret-cast-computation
  ; syntactic-value-irrelevant
  ; type-abstraction-computation
  )
open import Types


interpret-return-next :
  ∀ {W γ θ M V n} →
  interpret W γ θ M n ≡ returned W V →
  interpret W γ θ M (suc n) ≡ returned W V
interpret-return-next {W} {γ} {θ} {M} {V} {n} result-eq =
  subst
    (λ index → interpret W γ θ M index ≡ returned W V)
    (trans (+-suc n Data.Nat.zero)
      (cong suc (+-identityʳ n)))
    (interpret-terminal-stable
      {W = W} {γ = γ} {θ = θ} {M = M}
      {n = n} {o = returned W V}
      terminal-return result-eq (suc Data.Nat.zero))


inert-syntax-return :
  ∀ {W γ θ M c V n}
    {vM : N.Value M} {inert : C.Inert c}
    (body-return : interpret W γ θ M n ≡ returned W V)
    (execution :
      Runtime.InterpreterInertFrame.InertFrameExecution
        W θ c V inert) →
  interpret W γ θ (M N.⟨ c ⟩) (suc (suc n)) ≡
    returned W (result execution)
inert-syntax-return
    {W = W} {γ = γ} {θ = θ} {M = M}
    {c = c} {V = V} {n = n}
    body-return execution
  =
  trans
    (interpret-cast-computation
      {W = W} {γ = γ} {θ = θ} {M = M}
      {c = c} {n = suc n} {outcome = returned W V}
      (interpret-return-next
        {W = W} {γ = γ} {θ = θ} {M = M}
        {V = V} {n = n} body-return))
    (computes execution n)


closeValue-cast-body-success :
  ∀ {γ θ M c U}
    {vM : N.Value M} {inert : C.Inert c} →
  closeValue (vM N.⟨ inert ⟩) γ θ ≡ just U →
  Σ[ V ∈ Value ] closeValue vM γ θ ≡ just V
closeValue-cast-body-success
    {γ = γ} {θ} {vM = vM} {inert = G C.!} close-eq
    with ground? θ G | closeValue vM γ θ
closeValue-cast-body-success
    {γ = γ} {θ} {vM = vM} {inert = G C.!} close-eq
    | yes ground | just V =
  V , refl
closeValue-cast-body-success
    {γ = γ} {θ} {vM = vM} {inert = G C.!} ()
    | yes ground | nothing
closeValue-cast-body-success
    {γ = γ} {θ} {vM = vM} {inert = G C.!} ()
    | no not-ground | result
closeValue-cast-body-success
    {γ = γ} {θ} {vM = vM}
    {inert = C.seal A X} close-eq
    with lookup θ X | closeValue vM γ θ
closeValue-cast-body-success
    {γ = γ} {θ} {vM = vM}
    {inert = C.seal A X} close-eq
    | just (seal-name α) | just V =
  V , refl
closeValue-cast-body-success
    {γ = γ} {θ} {vM = vM}
    {inert = C.seal A X} ()
    | just (seal-name α) | nothing
closeValue-cast-body-success
    {γ = γ} {θ} {vM = vM}
    {inert = C.seal A X} ()
    | just (abstract-name Y) | result
closeValue-cast-body-success
    {γ = γ} {θ} {vM = vM}
    {inert = C.seal A X} ()
    | nothing | result
closeValue-cast-body-success
    {γ = γ} {θ} {vM = vM}
    {inert = p C.↦ q} close-eq
    with closeValue vM γ θ
closeValue-cast-body-success
    {γ = γ} {θ} {vM = vM}
    {inert = p C.↦ q} close-eq | just V =
  V , refl
closeValue-cast-body-success
    {γ = γ} {θ} {vM = vM}
    {inert = p C.↦ q} () | nothing
closeValue-cast-body-success
    {γ = γ} {θ} {vM = vM}
    {inert = C.`∀ c} close-eq
    with closeValue vM γ θ
closeValue-cast-body-success
    {γ = γ} {θ} {vM = vM}
    {inert = C.`∀ c} close-eq | just V =
  V , refl
closeValue-cast-body-success
    {γ = γ} {θ} {vM = vM}
    {inert = C.`∀ c} () | nothing
closeValue-cast-body-success
    {γ = γ} {θ} {vM = vM}
    {inert = C.gen A c} close-eq
    with closeValue vM γ θ
closeValue-cast-body-success
    {γ = γ} {θ} {vM = vM}
    {inert = C.gen A c} close-eq | just V =
  V , refl
closeValue-cast-body-success
    {γ = γ} {θ} {vM = vM}
    {inert = C.gen A c} () | nothing


typed-syntactic-value-eventually-returns :
  ∀ {W Δ Σ Γ γ θ M A U}
    (runtime : RuntimeContext W Δ Σ θ)
    (runtime-env : RuntimeTypeEnvironment θ)
    (vM : N.Value M) →
  N._∣_∣_⊢_⦂_ Δ Σ Γ M A →
  closeValue vM γ θ ≡ just U →
  Σ[ n ∈ StepIndex ] interpret W γ θ M n ≡ returned W U
typed-syntactic-value-eventually-returns runtime runtime-env
    (N.ƛ M) (N.⊢ƛ hA body) refl =
  suc Data.Nat.zero , refl
typed-syntactic-value-eventually-returns
    {W = W} {γ = γ} {θ} runtime
    runtime-env
    (N.Λ vM) (N.⊢Λ vM′ body) close-eq
    with syntacticValue-complete vM
typed-syntactic-value-eventually-returns
    {W = W} {γ = γ} {θ} runtime
    runtime-env
    (N.Λ vM) (N.⊢Λ vM′ body) close-eq
    | vM″ , decision-eq =
  suc Data.Nat.zero ,
  type-abstraction-computation vM
    (trans decision-eq
      (cong yes (syntactic-value-irrelevant vM″ vM)))
    close-eq (suc Data.Nat.zero)
typed-syntactic-value-eventually-returns runtime runtime-env
    (N.$ κ) (N.⊢$ .κ) refl =
  suc Data.Nat.zero , refl
typed-syntactic-value-eventually-returns
    {W = W} {γ = γ} {θ} runtime
    runtime-env
    (vM N.⟨ inert ⟩) (N.⊢⟨⟩ coercion body) close-eq
    with closeValue-cast-body-success
      {γ = γ} {θ = θ} {vM = vM} {inert = inert}
      close-eq
typed-syntactic-value-eventually-returns
    {W = W} {γ = γ} {θ} runtime
    runtime-env
    (vM N.⟨ inert ⟩) (N.⊢⟨⟩ coercion body) close-eq
    | V , body-close-eq
    with typed-syntactic-value-eventually-returns
      {W = W} {γ = γ} {θ = θ}
      runtime runtime-env vM body body-close-eq
typed-syntactic-value-eventually-returns
    {W = W} {γ = γ} {θ} runtime
    runtime-env
    (vM N.⟨ inert ⟩) (N.⊢⟨⟩ coercion body) close-eq
    | V , body-close-eq | n , body-return
    with execute-inert-frame runtime runtime-env coercion inert
typed-syntactic-value-eventually-returns
    {W = W} {γ = γ} {θ} {U = U} runtime
    runtime-env
    (vM N.⟨ inert ⟩) (N.⊢⟨⟩ coercion body) close-eq
    | V , body-close-eq | n , body-return
    | execution
    with syntactic-value-return-unique
      {W = W} {U = W} {γ = γ} {θ = θ}
      {V = U} {V′ = result execution}
      {n = suc (suc n)}
      (vM N.⟨ inert ⟩) close-eq
      (inert-syntax-return
        {W = W} {γ = γ} {θ = θ} {n = n}
        {vM = vM} {inert = inert}
        body-return execution)
typed-syntactic-value-eventually-returns
    {W = W} {γ = γ} {θ} {U = U} runtime
    runtime-env
    (vM N.⟨ inert ⟩) (N.⊢⟨⟩ coercion body) close-eq
    | V , body-close-eq | n , body-return
    | execution | refl , refl =
  suc (suc n) ,
  inert-syntax-return
    {W = W} {γ = γ} {θ = θ} {n = n}
    {vM = vM} {inert = inert}
    body-return execution

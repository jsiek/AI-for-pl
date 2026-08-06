module InterpreterAdequacy.proof.SmallStepReturnCompletenessBase where

-- File Charter:
--   * Proves the reflexive, already-a-value case of small-step return
--     completeness for closed interpreter terms.
--   * Constructs the semantic value by closing the official syntactic value
--     and returns a fuel index at which the direct interpreter produces it.
--   * Establishes the final value trace agreement without using a reduction
--     step; nonempty traces belong to the recursive completeness driver.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Data.List using ([])
open import Data.Maybe using (just; nothing)
open import Data.Nat using (suc; zero)
open import Data.Nat.Properties using (+-identityʳ; +-suc)
open import Data.Product using (_×_; Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)
open import Relation.Nullary using (no; yes)

import Coercions as C
open import Interpreter using
  ( RuntimeGround
  ; StepIndex
  ; Value
  ; abstract-name
  ; coerceValue
  ; emptyWorld
  ; ground?
  ; interpret
  ; lookup
  ; returned
  ; run
  ; runtime-ground-syntax
  ; seal-name
  )
open import InterpreterAdequacy.TraceAgreement
open import InterpreterAdequacy.proof.ClosedValueTrace using
  (closed-value-trace)
open import InterpreterAdequacy.proof.InitialTraceAgreement using
  (initial-term-trace-agreement)
open import InterpreterAdequacy.proof.InterpreterTermNoBullet using
  (interpreter-term-no-bullet)
open import InterpreterAdequacy.proof.TraceAgreementProperties using
  (empty-world-trace-agreement)
open import Core.InterpreterFuel using (interpret-terminal-stable)
open import Core.InterpreterOutcome using (terminal-return)
open import Typing.InterpreterSemanticTypingCore using (environment-empty)
open import SmallStepInterface.InterpreterTermShape using (InterpreterTerm)
open import NuReduction using (↠-refl; ↠-step; _—↠[_]_)
import NuTerms as N
open import proof.DGG.Core.NuReductionDeterminism using
  (value-irreducible)
open import proof.InterpreterClosedValueProof using (closeValue-closed)
open import proof.InterpreterCloseValueTyping using (closeValue-defined)
open import proof.InterpreterErrorFreedomCore using (empty-runtime-context)
open import proof.InterpreterSyntacticValueComputationProof using
  ( interpret-cast-computation
  ; syntactic-value-irrelevant
  ; type-abstraction-computation
  )
open import proof.InterpreterCloseValueTyping using
  (syntacticValue-complete)

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

interpret-cast-after-return :
  ∀ {W γ θ M c V U n} →
  interpret W γ θ M n ≡ returned W V →
  coerceValue W θ c V (suc n) ≡ returned W U →
  interpret W γ θ (M N.⟨ c ⟩) (suc (suc n)) ≡ returned W U
interpret-cast-after-return {W} {γ} {θ} {M} {c} {V} {U} {n}
    body-return coercion-return =
  trans
    (interpret-cast-computation
      {W = W} {γ = γ} {θ = θ} {M = M} {c = c}
      {n = suc n} {outcome = returned W V}
      (interpret-return-next
        {W = W} {γ = γ} {θ = θ} {M = M} {V = V} {n = n}
        body-return))
    coercion-return

tag-coercion-return : ∀ {W θ G V n runtime-ground}
  → ground? θ G ≡ yes runtime-ground
  → coerceValue W θ (G C.!) V (suc n) ≡
    returned W
      (Interpreter.tagged
        (runtime-ground-syntax runtime-ground) θ V)
tag-coercion-return ground-eq rewrite ground-eq =
  refl

seal-coercion-return :
  ∀ {W θ A X V n α} →
  lookup θ X ≡ just (seal-name α) →
  coerceValue W θ (C.seal A X) V (suc n) ≡
    returned W (Interpreter.sealed α V)
seal-coercion-return name-eq rewrite name-eq =
  refl

closed-value-eventually-returns :
  ∀ {W γ θ M V} →
  (vM : N.Value M) →
  Interpreter.closeValue vM γ θ ≡ just V →
  Σ[ n ∈ StepIndex ]
    interpret W γ θ M n ≡ returned W V
closed-value-eventually-returns (N.ƛ M) close-eq
    with close-eq
closed-value-eventually-returns (N.ƛ M) close-eq | refl =
  suc zero , refl
closed-value-eventually-returns {W = W} {γ = γ} {θ = θ}
    (N.Λ vM) close-eq
    with syntacticValue-complete vM
closed-value-eventually-returns {W = W} {γ = γ} {θ = θ}
    (N.Λ vM) close-eq | vM′ , decision-eq =
  suc zero ,
    type-abstraction-computation vM
      (trans decision-eq
        (cong yes (syntactic-value-irrelevant vM′ vM)))
      close-eq (suc zero)
closed-value-eventually-returns (N.$ κ) close-eq
    with close-eq
closed-value-eventually-returns (N.$ κ) close-eq | refl =
  suc zero , refl
closed-value-eventually-returns {W = W} {γ = γ} {θ = θ}
    {M = M N.⟨ G C.! ⟩}
    (vM N.⟨ G C.! ⟩) close-eq
    with ground? θ G in ground-eq | Interpreter.closeValue vM γ θ
      in body-eq
closed-value-eventually-returns (vM N.⟨ G C.! ⟩) ()
    | no not-ground | body-result
closed-value-eventually-returns (vM N.⟨ G C.! ⟩) ()
    | yes runtime-ground | nothing
closed-value-eventually-returns {W = W} {γ = γ} {θ = θ}
    {M = M N.⟨ G C.! ⟩}
    (vM N.⟨ G C.! ⟩) close-eq
    | yes runtime-ground | just U
    with close-eq
closed-value-eventually-returns {W = W} {γ = γ} {θ = θ}
    {M = M N.⟨ G C.! ⟩}
    (vM N.⟨ G C.! ⟩) close-eq
    | yes runtime-ground | just U | refl
    with closed-value-eventually-returns {W = W} vM body-eq
closed-value-eventually-returns {W = W} {γ = γ} {θ = θ}
    {M = M N.⟨ G C.! ⟩}
    (vM N.⟨ G C.! ⟩) close-eq
    | yes runtime-ground | just U | refl | n , body-return =
  suc (suc n) ,
    interpret-cast-after-return
      {W = W} {γ = γ} {θ = θ} {M = M} {c = G C.!}
      {V = U}
      {U = Interpreter.tagged
        (runtime-ground-syntax runtime-ground) θ U}
      {n = n} body-return
      (tag-coercion-return
        {W = W} {θ = θ} {G = G} {V = U} {n = n}
        {runtime-ground = runtime-ground} ground-eq)
closed-value-eventually-returns {W = W} {γ = γ} {θ = θ}
    {M = M N.⟨ C.seal A X ⟩}
    (vM N.⟨ C.seal A X ⟩) close-eq
    with lookup θ X in name-eq | Interpreter.closeValue vM γ θ
      in body-eq
closed-value-eventually-returns (vM N.⟨ C.seal A X ⟩) ()
    | nothing | body-result
closed-value-eventually-returns (vM N.⟨ C.seal A X ⟩) ()
    | just (abstract-name Y) | body-result
closed-value-eventually-returns (vM N.⟨ C.seal A X ⟩) ()
    | just (seal-name α) | nothing
closed-value-eventually-returns {W = W} {γ = γ} {θ = θ}
    (vM N.⟨ C.seal A X ⟩) close-eq
    | just (seal-name α) | just U
    with close-eq
closed-value-eventually-returns {W = W} {γ = γ} {θ = θ}
    (vM N.⟨ C.seal A X ⟩) close-eq
    | just (seal-name α) | just U | refl
    with closed-value-eventually-returns {W = W} vM body-eq
closed-value-eventually-returns {W = W} {γ = γ} {θ = θ}
    {M = M N.⟨ C.seal A X ⟩}
    (vM N.⟨ C.seal A X ⟩) close-eq
    | just (seal-name α) | just U | refl | n , body-return
    =
  suc (suc n) ,
    interpret-cast-after-return
      {W = W} {γ = γ} {θ = θ} {M = M}
      {c = C.seal A X} {V = U} {U = Interpreter.sealed α U}
      {n = n} body-return
      (seal-coercion-return
        {W = W} {θ = θ} {A = A} {X = X} {V = U}
        {n = n} {α = α} name-eq)
closed-value-eventually-returns {W = W} {γ = γ} {θ = θ}
    (vM N.⟨ p C.↦ q ⟩) close-eq
    with Interpreter.closeValue vM γ θ in body-eq
closed-value-eventually-returns (vM N.⟨ p C.↦ q ⟩) () | nothing
closed-value-eventually-returns {W = W} (vM N.⟨ p C.↦ q ⟩)
    close-eq | just U
    with close-eq
closed-value-eventually-returns {W = W} (vM N.⟨ p C.↦ q ⟩)
    close-eq | just U | refl
    with closed-value-eventually-returns {W = W} vM body-eq
closed-value-eventually-returns {W = W} {γ = γ} {θ = θ}
    {M = M N.⟨ p C.↦ q ⟩} (vM N.⟨ p C.↦ q ⟩)
    close-eq | just U | refl | n , body-return
    =
  suc (suc n) ,
    interpret-cast-after-return
      {W = W} {γ = γ} {θ = θ} {M = M} {c = p C.↦ q}
      {V = U} {U = Interpreter.function-proxy p q θ U}
      {n = n} body-return refl
closed-value-eventually-returns {W = W} {γ = γ} {θ = θ}
    (vM N.⟨ C.`∀ c ⟩) close-eq
    with Interpreter.closeValue vM γ θ in body-eq
closed-value-eventually-returns (vM N.⟨ C.`∀ c ⟩) () | nothing
closed-value-eventually-returns {W = W} (vM N.⟨ C.`∀ c ⟩)
    close-eq | just U
    with close-eq
closed-value-eventually-returns {W = W} (vM N.⟨ C.`∀ c ⟩)
    close-eq | just U | refl
    with closed-value-eventually-returns {W = W} vM body-eq
closed-value-eventually-returns {W = W} {γ = γ} {θ = θ}
    {M = M N.⟨ C.`∀ c ⟩} (vM N.⟨ C.`∀ c ⟩)
    close-eq | just U | refl | n , body-return
    =
  suc (suc n) ,
    interpret-cast-after-return
      {W = W} {γ = γ} {θ = θ} {M = M} {c = C.`∀ c}
      {V = U} {U = Interpreter.forall-proxy c θ U}
      {n = n} body-return refl
closed-value-eventually-returns {W = W} {γ = γ} {θ = θ}
    (vM N.⟨ C.gen A c ⟩) close-eq
    with Interpreter.closeValue vM γ θ in body-eq
closed-value-eventually-returns (vM N.⟨ C.gen A c ⟩) () | nothing
closed-value-eventually-returns {W = W} (vM N.⟨ C.gen A c ⟩)
    close-eq | just U
    with close-eq
closed-value-eventually-returns {W = W} (vM N.⟨ C.gen A c ⟩)
    close-eq | just U | refl
    with closed-value-eventually-returns {W = W} vM body-eq
closed-value-eventually-returns {W = W} {γ = γ} {θ = θ}
    {M = M N.⟨ C.gen A c ⟩} (vM N.⟨ C.gen A c ⟩)
    close-eq | just U | refl | n , body-return
    =
  suc (suc n) ,
    interpret-cast-after-return
      {W = W} {γ = γ} {θ = θ} {M = M} {c = C.gen A c}
      {V = U} {U = Interpreter.generalized A c θ U}
      {n = n} body-return refl

small-step-return-complete-reflᵢ :
  ∀ {M A} →
  (image : InterpreterTerm M) →
  (vM : N.Value M) →
  (M⊢ : N._∣_∣_⊢_⦂_ 0 [] [] M A) →
  Σ[ n ∈ Interpreter.StepIndex ]
  Σ[ V ∈ Value ]
    (run M n ≡ returned emptyWorld V) ×
    ValueTraceAgreement empty-world-trace-agreement [] V M
small-step-return-complete-reflᵢ {M = M} image vM M⊢
    with closeValue-defined empty-runtime-context environment-empty
      image vM M⊢
small-step-return-complete-reflᵢ {M = M} image vM M⊢
    | V , close-eq
    with closed-value-eventually-returns
      {W = emptyWorld} vM close-eq
small-step-return-complete-reflᵢ {M = M} image vM M⊢
    | V , close-eq | n , return-eq
    with initial-term-trace-agreement M⊢
small-step-return-complete-reflᵢ {M = M} image vM M⊢
    | V , close-eq | n , return-eq
    | term-trace-agreement τ vs θ-agrees γ-agrees reification =
  n , V , return-eq ,
    subst
      (ValueTraceAgreement empty-world-trace-agreement [] V)
      (sym reification)
      (closed-value-trace (closeValue-closed vM close-eq)
        θ-agrees γ-agrees (interpreter-term-no-bullet image))

small-step-return-complete-valueᵢ :
  ∀ {M A χs v} →
  (image : InterpreterTerm M) →
  (vM : N.Value M) →
  (M⊢ : N._∣_∣_⊢_⦂_ 0 [] [] M A) →
  M —↠[ χs ] v →
  N.Value v →
  Σ[ n ∈ StepIndex ]
  Σ[ V ∈ Value ]
  Σ[ world-agreement ∈ WorldTraceAgreement emptyWorld χs ]
    (run M n ≡ returned emptyWorld V) ×
    ValueTraceAgreement world-agreement [] V v
small-step-return-complete-valueᵢ image vM M⊢ ↠-refl vM′
    with small-step-return-complete-reflᵢ image vM M⊢
small-step-return-complete-valueᵢ image vM M⊢ ↠-refl vM′
    | n , V , return-eq , V-agrees =
  n , V , empty-world-trace-agreement , return-eq , V-agrees
small-step-return-complete-valueᵢ image vM M⊢
    (↠-step M→N N↠v) vM′ =
  ⊥-elim (value-irreducible vM M→N)

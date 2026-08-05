module proof.InterpreterTypeSoundnessProof where

-- File Charter:
--   * Proves type soundness for closed programs run by the direct,
--     fuel-indexed interpreter.
--   * Uses the same `NuTerms` typing judgment as the existing GTSF progress
--     and preservation proofs plus the compiler-image grammar; the latter
--     excludes the small-step-only runtime bullet.
--   * Classifies every run as timeout, blame, or a semantically typed value,
--     without using any reduction relation or reduction theorem.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([])
open import Data.Nat using (ℕ; zero)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (subst)

open import Interpreter
open import Typing.InterpreterSemanticTypingCore
open import SmallStepInterface.InterpreterTermShape using (InterpreterTerm)
open import proof.InterpreterErrorFreedomCore using
  (empty-runtime-context)
open import proof.InterpreterTypingCore using (interpret-typing)
import NuTerms as N

run-type-sound :
  ∀ n {M A} →
  InterpreterTerm M →
  N._∣_∣_⊢_⦂_ zero [] [] M A →
  (∃[ W ] run M n ≡ timed W) ⊎
  ((∃[ W ] run M n ≡ blamed W) ⊎
   (∃[ W ] ∃[ V ]
     (run M n ≡ returned W V) ×
     WorldTyping W × ValueTyping W V ⟦ A ⟧[ [] ]))
run-type-sound n {M = M} {A = A} image M⊢
    with run M n in run-eq
run-type-sound n image M⊢ | timed U =
  inj₁ (U , refl)
run-type-sound n image M⊢ | blamed U =
  inj₂ (inj₁ (U , refl))
run-type-sound n {A = A} image M⊢ | failed U e
    with subst (OutcomeTyping emptyWorld ⟦ A ⟧[ [] ]) run-eq
      (interpret-typing n empty-world-typed
        empty-runtime-context runtime-type-empty environment-empty
        image M⊢)
run-type-sound n {A = A} image M⊢ | failed U e | ()
run-type-sound n {A = A} image M⊢ | returned U V
    with subst (OutcomeTyping emptyWorld ⟦ A ⟧[ [] ]) run-eq
      (interpret-typing n empty-world-typed
        empty-runtime-context runtime-type-empty environment-empty
        image M⊢)
run-type-sound n {A = A} image M⊢ | returned U V
    | return-typed []≤U U⊢ V⊢ =
  inj₂ (inj₂ (U , V , refl , U⊢ , V⊢))

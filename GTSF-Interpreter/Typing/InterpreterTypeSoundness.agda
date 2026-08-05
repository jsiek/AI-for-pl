module Typing.InterpreterTypeSoundness where

-- File Charter:
--   * Public type-soundness theorem for the direct fuel-indexed interpreter.
--   * Uses the same `NuTerms` typing judgment as the existing GTSF progress
--     and preservation theorems, but uses none of their reduction results.
--   * Explicitly excludes the small-step-only runtime bullet via
--     `InterpreterTerm`, the grammar of compiled source programs.
--   * Its three result branches are timeout, blame, and a typed value; there
--     is deliberately no interpreter-error branch.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using ([])
open import Data.Nat using (zero)
open import Data.Product using (_×_; ∃; ∃-syntax)
open import Data.Sum using (_⊎_)

open import Interpreter
open import Typing.InterpreterSemanticTyping using
  (WorldTyping; ValueTyping; ⟦_⟧[_])
open import SmallStepInterface.InterpreterTermShape using (InterpreterTerm)
import NuTerms as N
import proof.InterpreterTypeSoundnessProof as Proof

interpreter-type-sound :
  ∀ n {M A} →
  InterpreterTerm M →
  N._∣_∣_⊢_⦂_ zero [] [] M A →
  (∃[ W ] run M n ≡ timed W) ⊎
  ((∃[ W ] run M n ≡ blamed W) ⊎
   (∃[ W ] ∃[ V ]
     (run M n ≡ returned W V) ×
     WorldTyping W × ValueTyping W V ⟦ A ⟧[ [] ]))
interpreter-type-sound =
  Proof.run-type-sound

module InterpreterAdequacy.Divergence where

-- File Charter:
--   * Public divergence-adequacy interface for closed, typed direct-
--     interpreter source terms.
--   * Equates timeout at every finite interpreter index with positive
--     small-step divergence.
--   * Delegates proof details to `proof.DivergenceProof`.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using ([])
open import Data.Nat using (zero)
open import Data.Product using (Σ-syntax)

open import Interpreter using (World; run; timed)
open import InterpreterAdequacy.DivergenceRelation public using (Diverges)
open import SmallStepInterface.InterpreterTermShape using (InterpreterTerm)
import InterpreterAdequacy.proof.DivergenceProof as Proof
import NuTerms as N

run-timeout-soundᵢ : ∀ {M A}
  → InterpreterTerm M
  → N._∣_∣_⊢_⦂_ zero [] [] M A
  → (∀ n → Σ[ W ∈ World ] run M n ≡ timed W)
  → Diverges M
run-timeout-soundᵢ =
  Proof.run-timeout-soundᵖ

small-step-divergence-completeᵢ : ∀ {M A}
  → InterpreterTerm M
  → N._∣_∣_⊢_⦂_ zero [] [] M A
  → Diverges M
  → ∀ n → Σ[ W ∈ World ] run M n ≡ timed W
small-step-divergence-completeᵢ =
  Proof.small-step-divergence-completeᵖ

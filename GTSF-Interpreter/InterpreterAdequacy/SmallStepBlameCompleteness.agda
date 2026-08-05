module InterpreterAdequacy.SmallStepBlameCompleteness where

-- File Charter:
--   * States the public small-step-to-interpreter blame-completeness theorem.
--   * Covers every finite trace from a closed, typed interpreter source term
--     to blame.
--   * Keeps the well-founded interpreter simulation in the private proof
--     layer.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using ([])
open import Data.Nat using (zero)
open import Data.Product using (Σ-syntax)

open import Interpreter using (StepIndex; World; blamed; run)
import InterpreterAdequacy.proof.SmallStepBlameCompleteness as Proof
open import SmallStepInterface.InterpreterTermShape using (InterpreterTerm)
open import NuReduction using (_—↠[_]_)
import NuTerms as N

small-step-blame-completeᵢ :
  ∀ {M A changes} →
  (image : InterpreterTerm M) →
  N._∣_∣_⊢_⦂_ zero [] [] M A →
  M —↠[ changes ] N.blame →
  Σ[ n ∈ StepIndex ] Σ[ W ∈ World ] run M n ≡ blamed W
small-step-blame-completeᵢ =
  Proof.small-step-blame-completeᵢ

module Runtime.InterpreterValueSubstitutionShape where

-- File Charter:
--   * Public outer-shape inversion for semantic name substitution.
--   * Shows that substitution cannot create a constant or sealed head.
--   * Delegates exhaustive value analysis to a private proof module.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Product using (Σ-syntax)

open import Interpreter
import proof.InterpreterValueSubstitutionShapeProof as Proof
open import Types

substitute-name-sealed-source :
  ∀ (X : Name) (α : SealName) (V : Value) {β U} →
  substituteName X α V ≡ sealed β U →
  Σ[ Q ∈ Value ] V ≡ sealed β Q
substitute-name-sealed-source =
  Proof.substitute-name-sealed-source

substitute-name-constant-source :
  ∀ (X : Name) (α : SealName) (V : Value) {κ} →
  substituteName X α V ≡ constant κ →
  V ≡ constant κ
substitute-name-constant-source =
  Proof.substitute-name-constant-source

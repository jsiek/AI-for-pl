module proof.TypeSafety.IrreducibleProof where

-- File Charter:
--   * Proves that GTNF values and blame cannot reduce.
--   * Uses the value inversion already checked beside the reduction relation;
--     blame has no reduction constructor at the root.

open import Data.Product using (_,_)
open import Data.Empty using (⊥)

open import Terms using (blame)
open import Reduction using (_⊢_-→_∣_; value-¬step)
open import proof.TypeSafety.IrreducibleDef

blame-¬step : ∀ {Δ M′ δ ℓ} → Δ ⊢ blame ℓ -→ M′ ∣ δ → ⊥
blame-¬step ()

irreducible : Irreducible-Statement
irreducible = value-¬step , blame-¬step

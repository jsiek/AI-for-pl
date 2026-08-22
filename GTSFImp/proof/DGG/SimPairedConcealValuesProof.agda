module proof.DGG.SimPairedConcealValuesProof where

-- File Charter:
--   * Implements the paired conceal value simulation interface.
--   * Refutes source value steps for pivoted conceal conversions.
--   * Does not alter the conceal relation or reduction rules.

open import Data.Empty using (⊥-elim)

open import Reduction using (pure-step; blame-conceal; ξ-conceal)
import Conversion as Conv
open import proof.DGG.SimPairedConcealValuesDef
  using (SimPairedConcealValuesᵀ)
open import proof.Reduction.ValueIrreducibleProof
  using (value-no-step)


sim-paired-conceal-values : SimPairedConcealValuesᵀ
sim-paired-conceal-values _ _ _ _ (Conv.⊢↓-sealˣ _) _ _ _ ()
    (pure-step blame-conceal) _
sim-paired-conceal-values _ _ _ _ (Conv.⊢↓-sealˣ _) _ _ _ vV
    (ξ-conceal step _) _ =
  ⊥-elim (value-no-step vV step)
sim-paired-conceal-values _ _ _ _ (Conv.⊢↓-⇒ˣ _ _ _) _ _ _ ()
    (pure-step blame-conceal) _
sim-paired-conceal-values _ _ _ _ (Conv.⊢↓-⇒ˣ _ _ _) _ _ _ vV
    (ξ-conceal step _) _ =
  ⊥-elim (value-no-step vV step)
sim-paired-conceal-values _ _ _ _ (Conv.⊢↓-∀ˣ _) _ _ _ ()
    (pure-step blame-conceal) _
sim-paired-conceal-values _ _ _ _ (Conv.⊢↓-∀ˣ _) _ _ _ vV
    (ξ-conceal step _) _ =
  ⊥-elim (value-no-step vV step)

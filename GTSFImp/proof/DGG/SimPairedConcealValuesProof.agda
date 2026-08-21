module proof.DGG.SimPairedConcealValuesProof where

-- File Charter:
--   * Implements the paired conceal value simulation interface.
--   * Eliminates identity roots from generator nonabsence, then refutes source
--     value steps for active conceal conversions.
--   * Does not alter the conceal relation or reduction rules.

open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (refl)

open import Reduction using (pure-step; blame-conceal; ξ-conceal)
import Conversion as Conv
open import proof.DGG.SimPairedConcealValuesDef
  using (SimPairedConcealValuesᵀ)
open import proof.Reduction.ValueIrreducibleProof
  using (value-no-step)


sim-paired-conceal-values : SimPairedConcealValuesᵀ
sim-paired-conceal-values _ (Conv.⊢↓-seal _) _ _ _ _ _ _ _ _ ()
    (pure-step blame-conceal) _
sim-paired-conceal-values _ (Conv.⊢↓-seal _) _ _ _ _ _ _ _ _ vV
    (ξ-conceal step _) _ =
  ⊥-elim (value-no-step vV step)
sim-paired-conceal-values _ (Conv.⊢↓-⇒ _ _) _ _ _ _ _ _ _ _ ()
    (pure-step blame-conceal) _
sim-paired-conceal-values _ (Conv.⊢↓-⇒ _ _) _ _ _ _ _ _ _ _ vV
    (ξ-conceal step _) _ =
  ⊥-elim (value-no-step vV step)
sim-paired-conceal-values _ (Conv.⊢↓-∀ _ _) _ _ _ _ _ _ _ _ ()
    (pure-step blame-conceal) _
sim-paired-conceal-values _ (Conv.⊢↓-∀ _ _) _ _ _ _ _ _ _ _ vV
    (ξ-conceal step _) _ =
  ⊥-elim (value-no-step vV step)
sim-paired-conceal-values _ (Conv.⊢↓-id-var _ _) _ _ nonabsent
    _ _ _ _ _ _ _ _ =
  ⊥-elim (nonabsent refl)
sim-paired-conceal-values _ (Conv.⊢↓-id-base _) _ _ nonabsent
    _ _ _ _ _ _ _ _ =
  ⊥-elim (nonabsent refl)
sim-paired-conceal-values _ (Conv.⊢↓-id-star _) _ _ nonabsent
    _ _ _ _ _ _ _ _ =
  ⊥-elim (nonabsent refl)

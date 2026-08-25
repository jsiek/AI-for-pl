module ImprecisionComposition where

-- File Charter:
--   * Publicly exposes transitivity of GTSFImp type imprecision.
--   * States the theorem explicitly and delegates its proof to
--     proof.ImprecisionComposition.
--   * Depends only on Types, Imprecision, and the private proof module.

open import Types
import Imprecision as I
import proof.ImprecisionComposition as P


⊑-trans : ∀ {Δ} {μ : I.ImpEnv Δ} {A B C : Ty Δ}
  → I._⊢_⊑_ μ A B
  → I._⊢_⊑_ μ B C
  → I._⊢_⊑_ μ A C
⊑-trans = P.⊑-trans

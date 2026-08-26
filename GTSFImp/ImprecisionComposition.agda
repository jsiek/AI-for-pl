module ImprecisionComposition where

-- File Charter:
--   * Publicly exposes transitivity of GTSFImp type imprecision.
--   * States the theorem explicitly and delegates its proof to
--     proof.ImprecisionComposition.
--   * Depends only on Types, Imprecision, and the private proof module.

open import Types
open import Imprecision
import proof.ImprecisionComposition as P


⊑-trans : ∀ {Δ} {μ : ImpEnv Δ} {A B C : Ty Δ}
  → μ ⊢ A ⊑ B
  → μ ⊢ B ⊑ C
  → μ ⊢ A ⊑ C
⊑-trans = P.⊑-trans

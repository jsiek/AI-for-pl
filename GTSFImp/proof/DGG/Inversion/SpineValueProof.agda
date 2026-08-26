module proof.DGG.Inversion.SpineValueProof where

-- File Charter:
--   * Proves that target polymorphic value views survive type renaming.
--   * Rebuilds generated-cast safety at the renamed endpoints.
--   * Supplies the weakening bridge used by structural M5 instantiation.

open import Relation.Binary.PropositionalEquality using (_≢_; refl)

open import Types
open import Consistency using
  (_↪ᵗ_; keep; toRenameᵗ)
import CastTerms as CT
open import CastTerms using (renameᵗᵐ)
open import proof.Consistency using (gen-safe)
open import proof.TypeInTermSubst using
  (rename-occurs; rename-star-injective; renameᵗᵐ-preserves-Value)
open import proof.DGG.Inversion.SpineValueDef


rename-all-value-view : ∀ {Δ Δ′} {V : CT.Term Δ}
  → (rho : Δ ↪ᵗ Δ′)
  → AllValueView V
  → AllValueView (renameᵗᵐ rho V)
rename-all-value-view rho (allv-Λ vW refl) =
  allv-Λ (renameᵗᵐ-preserves-Value (keep rho) vW) refl
rename-all-value-view rho (allv-∀ vW refl) =
  allv-∀ (renameᵗᵐ-preserves-Value rho vW) refl
rename-all-value-view rho
    (allv-gen {A = A} {B = B} ⦃ Bnv ⦄ ⦃ z∈B ⦄
      vW A≢★ safe refl) =
  allv-gen
    ⦃ Bnv = _ ⦄
    ⦃ z∈B = _ ⦄
    (renameᵗᵐ-preserves-Value rho vW)
    A′≢★
    (gen-safe _ A′≢★ (renameNonVar _ Bnv) (rename-occurs _ z∈B))
    refl
  where
  A′≢★ : renameᵗ (toRenameᵗ rho) A ≢ ★
  A′≢★ eq = A≢★ (rename-star-injective (toRenameᵗ rho) eq)
rename-all-value-view rho (allv-reveal vW refl) =
  allv-reveal (renameᵗᵐ-preserves-Value rho vW) refl
rename-all-value-view rho (allv-conceal vW refl) =
  allv-conceal (renameᵗᵐ-preserves-Value rho vW) refl

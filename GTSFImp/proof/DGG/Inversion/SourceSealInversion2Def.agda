{-# OPTIONS --safe #-}

module proof.DGG.Inversion.SourceSealInversion2Def where

-- File Charter:
--   * States inversion of an unmatched source seal between related values.
--   * Retains the source-only occupancy, representation, and store evidence
--     that justifies exposing the sealed representation type.
--   * Contains no seal-inversion proof.

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

open import Types using (Ty; TyVar; ★; ＇_)
open import TyStore using (_∋_⦂_)
open import Consistency using (toRenameᵗ)
open import CastTerms using
  (Ctx; Δᵉ; Σᵉ; Term; Value; _↓_)
open import Conversion using (seal)
open import Imprecision using (X⊑★)
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.DGG.World


SourceSealInversion² : Set
SourceSealInversion² =
  ∀ {Γᴸ Γᴿ : Ctx} {γ : Γᴸ ⊑ᶜ Γᴿ}
    {V : Term (Δᵉ Γᴸ)} {V′ : Term (Δᵉ Γᴿ)}
    {Xᴸ : TyVar (Δᵉ Γᴸ)}
    {Rᴸ : Ty (Δᵉ Γᴸ)} {B : Ty (Δᵉ Γᴿ)}
    {p : ＇ Xᴸ ⊑ᵀ⟨ γ ⟩ B}
  → marksᶜ γ (toRenameⁱ (ηᴸᶜ γ) Xᴸ) ≡ X⊑★
  → (∀ Xᴿ → toRenameⁱ (ηᴿᶜ γ) Xᴿ
      ≢ toRenameⁱ (ηᴸᶜ γ) Xᴸ)
  → Rᴸ ⊑ᵀ⟨ γ ⟩ ★
  → Σᵉ Γᴸ ∋ Xᴸ ⦂ Rᴸ
  → Value V
  → Value V′
  → γ ⊢² V ↓ seal Xᴸ Rᴸ ⊑ V′ ∶ p
  → (q : Rᴸ ⊑ᵀ⟨ γ ⟩ B)
  → γ ⊢² V ⊑ V′ ∶ q

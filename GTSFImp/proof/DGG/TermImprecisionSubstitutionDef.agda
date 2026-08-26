{-# OPTIONS --safe #-}

module proof.DGG.TermImprecisionSubstitutionDef where

-- File Charter:
--   * States single-variable substitution for canonical cast-term
--     imprecision.
--   * Relates the two substituted bodies using the relation between the two
--     substituted values and the term-bound world of the body derivation.
--   * Contains no substitution proof.

open import Types using (Ty)
open import CastTerms using (Ctx; Δᵉ; Term; _[_])
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.DGG.World


TermImprecisionSubstitutionᵀ : Set
TermImprecisionSubstitutionᵀ = ∀ {Γᴸ Γᴿ : Ctx}
    {γ : Γᴸ ⊑ᶜ Γᴿ}
    {V : Term (Δᵉ Γᴸ)} {V′ : Term (Δᵉ Γᴿ)}
    {N : Term (Δᵉ Γᴸ)} {N′ : Term (Δᵉ Γᴿ)}
    {A B : Ty (Δᵉ Γᴸ)} {A′ B′ : Ty (Δᵉ Γᴿ)}
    {pA : A ⊑ᵀ⟨ γ ⟩ A′} {pB : B ⊑ᵀ⟨ γ ⟩ B′}
  → γ ⊢² V ⊑ V′ ∶ pA
  → bind-termᶜ γ pA ⊢² N ⊑ N′ ∶ pB
  → γ ⊢² N [ V ] ⊑ N′ [ V′ ] ∶ pB

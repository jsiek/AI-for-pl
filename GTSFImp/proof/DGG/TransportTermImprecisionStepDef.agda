{-# OPTIONS --safe #-}

module proof.DGG.TransportTermImprecisionStepDef where

-- File Charter:
--   * States the four structural allocation transports used by canonical
--     one-step cast-term-imprecision transport.
--   * Separates source, target, paired-precise, and paired-dynamic extension
--     because each requires its own induction through world history.
--   * Contains no result wrapper, classifier, compatibility world, or proof.

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
import Data.Nat as Nat

open import Types using (Ty; ★; ⇑ᵗ)
open import TyStore using (TyStore)
open import TermCtx using (TermCtx; ⇑ᶜ)
open import CastTerms using (Term; ⟨_,_,_⟩; ⇑ᵗᵐ)
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.DGG.World
open import proof.DGG.WorldEvolution using
  (evolution-bind-left; evolution-bind-right; evolution-bind-both;
   evolution-bind-both-star; evolution-⊑ᵀ)


TransportSourceBindᵀ : Set
TransportSourceBindᵀ = ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {Γᴸ⁺ : TermCtx (Nat.suc Δᴸ)} {C : Ty Δᴸ}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵀ⟨ γ ⟩ B}
  → sourceRebaseCountᶜ γ ≡ Nat.zero
  → (eqᴸ : Γᴸ⁺ ≡ ⇑ᶜ Γᴸ)
  → γ ⊢² M ⊑ M′ ∶ p
  → (γ ▻ᶜ bind-left-changeᶜ C eqᴸ) ⊢² ⇑ᵗᵐ M ⊑ M′
      ∶ evolution-⊑ᵀ
        (evolution-bind-left {A = C} {W = γ} eqᴸ) p


TransportTargetBindᵀ : Set
TransportTargetBindᵀ = ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {Γᴿ⁺ : TermCtx (Nat.suc Δᴿ)} {C : Ty Δᴿ}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵀ⟨ γ ⟩ B}
  → (fresh : RightBindFreshᶜ γ C)
  → (eqᴿ : Γᴿ⁺ ≡ ⇑ᶜ Γᴿ)
  → γ ⊢² M ⊑ M′ ∶ p
  → (γ ▻ᶜ bind-right-changeᶜ C fresh eqᴿ) ⊢² M ⊑ ⇑ᵗᵐ M′
      ∶ evolution-⊑ᵀ
        (evolution-bind-right {B = C} {W = γ} fresh eqᴿ) p


TransportPairedBindᵀ : Set
TransportPairedBindᵀ = ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {Γᴸ⁺ : TermCtx (Nat.suc Δᴸ)}
    {Γᴿ⁺ : TermCtx (Nat.suc Δᴿ)}
    {C : Ty Δᴸ} {D : Ty Δᴿ}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵀ⟨ γ ⟩ B}
  → (represented : C ⊑ᵀ⟨ γ ⟩ D)
  → (eqᴸ : Γᴸ⁺ ≡ ⇑ᶜ Γᴸ)
  → (eqᴿ : Γᴿ⁺ ≡ ⇑ᶜ Γᴿ)
  → γ ⊢² M ⊑ M′ ∶ p
  → (γ ▻ᶜ bind-both-changeᶜ represented eqᴸ eqᴿ) ⊢²
      ⇑ᵗᵐ M ⊑ ⇑ᵗᵐ M′
      ∶ evolution-⊑ᵀ
        (evolution-bind-both {W = γ} represented eqᴸ eqᴿ) p


TransportPairedStarBindᵀ : Set
TransportPairedStarBindᵀ = ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {Γᴸ⁺ : TermCtx (Nat.suc Δᴸ)}
    {Γᴿ⁺ : TermCtx (Nat.suc Δᴿ)}
    {C : Ty Δᴸ} {D : Ty Δᴿ}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵀ⟨ γ ⟩ B}
  → (represented : C ⊑ᵀ⟨ γ ⟩ D)
  → (C≠★ : ⇑ᵗ C ≢ ★)
  → (eqᴸ : Γᴸ⁺ ≡ ⇑ᶜ Γᴸ)
  → (eqᴿ : Γᴿ⁺ ≡ ⇑ᶜ Γᴿ)
  → γ ⊢² M ⊑ M′ ∶ p
  → (γ ▻ᶜ
      bind-both-star-changeᶜ represented C≠★ eqᴸ eqᴿ) ⊢²
      ⇑ᵗᵐ M ⊑ ⇑ᵗᵐ M′
      ∶ evolution-⊑ᵀ
        (evolution-bind-both-star
          {W = γ} represented C≠★ eqᴸ eqᴿ) p

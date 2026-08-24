{-# OPTIONS --safe #-}

module proof.DGG.WorldEvolution where

-- File Charter:
--   * Defines endpoint-indexed one-step world evolution for trusted store
--     changes without placing applyStore or another defined function in a
--     data-constructor index.
--   * Separates constructor-form endpoint change from its executable store
--     and term-context projections.
--   * Covers keep, left-only, right-only, paired-precise, and paired-dynamic
--     allocation as live World changes.
--   * Exports CtxChange, WorldEvolution, and their endpoint projections;
--     depends on World and the preservation context action.

open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Types using (Ty; ★; ⇑ᵗ)
open import TyStore using (TyStore; store-bind)
import TermCtx as TC
open TC using (TermCtx)
open import CastTerms using (Ctx; ⟨_,_,_⟩; Σᵉ; Γᵉ)
import Reduction as R
open import proof.TypeSafety.Preservation using (applyTermCtx)
open import proof.DGG.World


data CtxChange : Ctx → Ctx → Set where
  keep-ctx : ∀ {C}
    → CtxChange C C

  bind-ctx : ∀ {Δ} {Σ : TyStore Δ} {Γ : TermCtx Δ}
      {A : Ty Δ} {Γ⁺ : TermCtx (suc Δ)}
    → Γ⁺ ≡ TC.⇑ᶜ Γ
    → CtxChange
        ⟨ Δ , Σ , Γ ⟩
        ⟨ suc Δ , store-bind Σ A , Γ⁺ ⟩


storeChange : ∀ {C C′}
  → CtxChange C C′
  → R.StoreChange (CastTerms.Δᵉ C) (CastTerms.Δᵉ C′)
storeChange keep-ctx = R.keep
storeChange (bind-ctx {A = A} eq) = R.bind A


ctx-change-store : ∀ {C C′} (step : CtxChange C C′)
  → Σᵉ C′ ≡ R.applyStore (storeChange step) (Σᵉ C)
ctx-change-store keep-ctx = refl
ctx-change-store (bind-ctx eq) = refl


ctx-change-term : ∀ {C C′} (step : CtxChange C C′)
  → Γᵉ C′ ≡ applyTermCtx (storeChange step) (Γᵉ C)
ctx-change-term keep-ctx = refl
ctx-change-term (bind-ctx eq) = eq


data WorldEvolution : ∀ {Cᴸ Cᴿ Cᴸ′ Cᴿ′}
    {W : Cᴸ ⊑ᶜ Cᴿ} {W′ : Cᴸ′ ⊑ᶜ Cᴿ′}
  → CtxChange Cᴸ Cᴸ′
  → CtxChange Cᴿ Cᴿ′
  → Set where
  evolution-keep : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ}
    → WorldEvolution {W = W} {W′ = W} keep-ctx keep-ctx

  evolution-bind-left : ∀
      {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {Γᴸ⁺ : TermCtx (suc Δᴸ)} {A : Ty Δᴸ}
      {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      (eqᴸ : Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ)
    → WorldEvolution
        {W = W} {W′ = W ▻ᶜ bind-left-changeᶜ A eqᴸ}
        (bind-ctx eqᴸ) keep-ctx

  evolution-bind-right : ∀
      {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {Γᴿ⁺ : TermCtx (suc Δᴿ)} {B : Ty Δᴿ}
      {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      (fresh : RightBindFreshᶜ W B)
      (eqᴿ : Γᴿ⁺ ≡ TC.⇑ᶜ Γᴿ)
    → WorldEvolution
        {W = W} {W′ = W ▻ᶜ bind-right-changeᶜ B fresh eqᴿ}
        keep-ctx (bind-ctx eqᴿ)

  evolution-bind-both : ∀
      {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {Γᴸ⁺ : TermCtx (suc Δᴸ)} {Γᴿ⁺ : TermCtx (suc Δᴿ)}
      {A : Ty Δᴸ} {B : Ty Δᴿ}
      {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      (represented : A ⊑ᵀ⟨ W ⟩ B)
      (eqᴸ : Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ)
      (eqᴿ : Γᴿ⁺ ≡ TC.⇑ᶜ Γᴿ)
    → WorldEvolution
        {W = W} {W′ = W ▻ᶜ
          bind-both-changeᶜ represented eqᴸ eqᴿ}
        (bind-ctx eqᴸ) (bind-ctx eqᴿ)

  evolution-bind-both-star : ∀
      {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {Γᴸ⁺ : TermCtx (suc Δᴸ)} {Γᴿ⁺ : TermCtx (suc Δᴿ)}
      {A : Ty Δᴸ} {B : Ty Δᴿ}
      {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      (represented : A ⊑ᵀ⟨ W ⟩ B)
      (A≠★ : ⇑ᵗ A ≢ ★)
      (eqᴸ : Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ)
      (eqᴿ : Γᴿ⁺ ≡ TC.⇑ᶜ Γᴿ)
    → WorldEvolution
        {W = W}
        {W′ = W ▻ᶜ
          bind-both-star-changeᶜ represented A≠★ eqᴸ eqᴿ}
        (bind-ctx eqᴸ) (bind-ctx eqᴿ)


empty-evolution : WorldEvolution
    {W = emptyᶜ} {W′ = emptyᶜ} keep-ctx keep-ctx
empty-evolution = evolution-keep

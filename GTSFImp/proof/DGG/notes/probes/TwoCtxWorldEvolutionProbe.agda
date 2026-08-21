{-# OPTIONS --safe #-}

module proof.DGG.notes.probes.TwoCtxWorldEvolutionProbe where

-- File Charter:
--   * Checks endpoint-indexed one-step world evolution for trusted store
--     changes without placing applyStore or another defined function in a
--     data-constructor index.
--   * Separates constructor-form endpoint change from its executable store
--     and term-context projections.
--   * Covers keep, left-only, right-only, paired-precise, and paired-dynamic
--     allocation and derives direct invariants for every result.

open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Types using (Ty; ★; ⇑ᵗ)
open import TyStore using (TyStore; store-bind)
import TermCtx as TC
open TC using (TermCtx)
open import CastTerms using (Ctx; ⟨_,_,_⟩; Σᵉ; Γᵉ)
import Reduction as R
open import proof.DGG.notes.probes.TwoCtxWorldSkeletonProbe
open import proof.DGG.notes.probes.TwoCtxWorldInvariantsProbe


data CtxChangeᶜ₀ : Ctx → Ctx → Set where
  keep-ctxᶜ₀ : ∀ {C}
    → CtxChangeᶜ₀ C C

  bind-ctxᶜ₀ : ∀ {Δ} {Σ : TyStore Δ} {Γ : TermCtx Δ}
      {A : Ty Δ} {Γ⁺ : TermCtx (suc Δ)}
    → Γ⁺ ≡ TC.⇑ᶜ Γ
    → CtxChangeᶜ₀
        ⟨ Δ , Σ , Γ ⟩
        ⟨ suc Δ , store-bind Σ A , Γ⁺ ⟩


storeChangeᶜ₀ : ∀ {C C′}
  → CtxChangeᶜ₀ C C′
  → R.StoreChange (CastTerms.Δᵉ C) (CastTerms.Δᵉ C′)
storeChangeᶜ₀ keep-ctxᶜ₀ = R.keep
storeChangeᶜ₀ (bind-ctxᶜ₀ {A = A} eq) = R.bind A


applyTermCtxᶜ₀ : ∀ {Δ Δ′}
  → R.StoreChange Δ Δ′
  → TermCtx Δ
  → TermCtx Δ′
applyTermCtxᶜ₀ R.keep Γ = Γ
applyTermCtxᶜ₀ (R.bind A) Γ = TC.⇑ᶜ Γ


ctx-change-storeᶜ₀ : ∀ {C C′} (step : CtxChangeᶜ₀ C C′)
  → Σᵉ C′ ≡ R.applyStore (storeChangeᶜ₀ step) (Σᵉ C)
ctx-change-storeᶜ₀ keep-ctxᶜ₀ = refl
ctx-change-storeᶜ₀ (bind-ctxᶜ₀ eq) = refl


ctx-change-termᶜ₀ : ∀ {C C′} (step : CtxChangeᶜ₀ C C′)
  → Γᵉ C′ ≡ applyTermCtxᶜ₀ (storeChangeᶜ₀ step) (Γᵉ C)
ctx-change-termᶜ₀ keep-ctxᶜ₀ = refl
ctx-change-termᶜ₀ (bind-ctxᶜ₀ eq) = eq


data WorldEvolutionᶜ₀ : ∀ {Cᴸ Cᴿ Cᴸ′ Cᴿ′}
    {W : Cᴸ ⊑ᶜ₀ Cᴿ} {W′ : Cᴸ′ ⊑ᶜ₀ Cᴿ′}
  → CtxChangeᶜ₀ Cᴸ Cᴸ′
  → CtxChangeᶜ₀ Cᴿ Cᴿ′
  → Set where
  evolution-keepᶜ₀ : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ₀ Cᴿ}
    → WorldEvolutionᶜ₀ {W = W} {W′ = W} keep-ctxᶜ₀ keep-ctxᶜ₀

  evolution-bind-leftᶜ₀ : ∀
      {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {Γᴸ⁺ : TermCtx (suc Δᴸ)} {A : Ty Δᴸ}
      {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ₀ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      (eqᴸ : Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ)
    → WorldEvolutionᶜ₀
        {W = W} {W′ = bind-left-rawᶜ₀ W A eqᴸ}
        (bind-ctxᶜ₀ eqᴸ) keep-ctxᶜ₀

  evolution-bind-rightᶜ₀ : ∀
      {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {Γᴿ⁺ : TermCtx (suc Δᴿ)} {B : Ty Δᴿ}
      {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ₀ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      (fresh : RightBindFreshᶜ₀ W B)
      (eqᴿ : Γᴿ⁺ ≡ TC.⇑ᶜ Γᴿ)
    → WorldEvolutionᶜ₀
        {W = W} {W′ = bind-right-rawᶜ₀ W B fresh eqᴿ}
        keep-ctxᶜ₀ (bind-ctxᶜ₀ eqᴿ)

  evolution-bind-bothᶜ₀ : ∀
      {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {Γᴸ⁺ : TermCtx (suc Δᴸ)} {Γᴿ⁺ : TermCtx (suc Δᴿ)}
      {A : Ty Δᴸ} {B : Ty Δᴿ}
      {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ₀ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      (represented : A ⊑ᵀ₀⟨ W ⟩ B)
      (eqᴸ : Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ)
      (eqᴿ : Γᴿ⁺ ≡ TC.⇑ᶜ Γᴿ)
    → WorldEvolutionᶜ₀
        {W = W} {W′ = bind-both-rawᶜ₀ W represented eqᴸ eqᴿ}
        (bind-ctxᶜ₀ eqᴸ) (bind-ctxᶜ₀ eqᴿ)

  evolution-bind-both-starᶜ₀ : ∀
      {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {Γᴸ⁺ : TermCtx (suc Δᴸ)} {Γᴿ⁺ : TermCtx (suc Δᴿ)}
      {A : Ty Δᴸ} {B : Ty Δᴿ}
      {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ₀ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      (represented : A ⊑ᵀ₀⟨ W ⟩ B)
      (A≠★ : ⇑ᵗ A ≢ ★)
      (eqᴸ : Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ)
      (eqᴿ : Γᴿ⁺ ≡ TC.⇑ᶜ Γᴿ)
    → WorldEvolutionᶜ₀
        {W = W}
        {W′ = bind-both-star-rawᶜ₀ W represented A≠★ eqᴸ eqᴿ}
        (bind-ctxᶜ₀ eqᴸ) (bind-ctxᶜ₀ eqᴿ)


evolution-invariantsᶜ₀ : ∀ {Cᴸ Cᴿ Cᴸ′ Cᴿ′}
    {W : Cᴸ ⊑ᶜ₀ Cᴿ} {W′ : Cᴸ′ ⊑ᶜ₀ Cᴿ′}
    {stepᴸ : CtxChangeᶜ₀ Cᴸ Cᴸ′}
    {stepᴿ : CtxChangeᶜ₀ Cᴿ Cᴿ′}
  → WorldEvolutionᶜ₀ {W = W} {W′ = W′} stepᴸ stepᴿ
  → DirectWorldInvariantsᶜ₀ W′
evolution-invariantsᶜ₀ evolution-keepᶜ₀ = directInvariantsᶜ₀ _
evolution-invariantsᶜ₀ (evolution-bind-leftᶜ₀ eqᴸ) =
  directInvariantsᶜ₀ _
evolution-invariantsᶜ₀ (evolution-bind-rightᶜ₀ fresh eqᴿ) =
  directInvariantsᶜ₀ _
evolution-invariantsᶜ₀ (evolution-bind-bothᶜ₀ represented eqᴸ eqᴿ) =
  directInvariantsᶜ₀ _
evolution-invariantsᶜ₀
    (evolution-bind-both-starᶜ₀ represented A≠★ eqᴸ eqᴿ) =
  directInvariantsᶜ₀ _


empty-evolutionᶜ₀ : WorldEvolutionᶜ₀
    {W = emptyᶜ₀} {W′ = emptyᶜ₀} keep-ctxᶜ₀ keep-ctxᶜ₀
empty-evolutionᶜ₀ = evolution-keepᶜ₀

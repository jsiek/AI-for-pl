{-# OPTIONS --safe #-}

module proof.DGG.notes.probes.TwoCtxSimulationResultProbe where

-- File Charter:
--   * Checks a two-Ctx multi-step simulation-result interface whose final
--     runtime and term contexts are the endpoints of world evolution itself.
--   * Derives endpoint typing and executable transport projections from the
--     retained MultiWorldEvolution witness, with no SameRuntime or SameCtx.
--   * Checks the complete result choice: a synchronized endpoint package or a
--     source-blame trace.  It states no simulation proof and leaves the final
--     term relation as a parameter of the interface.

open import Data.List using ([])
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; subst)

open import Types using (Ty)
open import TyStore using (TyStore)
import TermCtx as TC
open import CastTerms using
  (Ctx; ⟨_,_,_⟩; Δᵉ; Σᵉ; Γᵉ; Term; blame; _⊢_⦂_)
import Reduction as R
open import Reduction using (_—↠[_]_)
  renaming ([] to []ˢ; _∷_ to _∷ˢ_)
import proof.TypeSafety.Preservation as Preservation
open Preservation using (multi-preservation)
open import proof.DGG.TwoCtxWorld
open import proof.DGG.notes.probes.TwoCtxWorldEvolutionSequenceProbe


preservation-term-context-agreesᶜ₀ : ∀ {Δ Δ′}
    (changes : R.StoreChanges Δ Δ′) Γ
  → Preservation.applyTermCtxs changes Γ ≡ applyTermCtxsᶜ₀ changes Γ
preservation-term-context-agreesᶜ₀ []ˢ Γ =
  sym (Preservation.applyTermCtxs-id Γ)
preservation-term-context-agreesᶜ₀ (R.keep ∷ˢ changes) Γ =
  trans (sym (Preservation.applyTermCtxs-step R.keep changes Γ))
    (preservation-term-context-agreesᶜ₀ changes Γ)
preservation-term-context-agreesᶜ₀ (R.bind A ∷ˢ changes) Γ =
  trans (sym (Preservation.applyTermCtxs-step (R.bind A) changes Γ))
    (preservation-term-context-agreesᶜ₀ changes (TC.⇑ᶜ Γ))


source-endpoint-typingᶜ₀ : ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Cᴸ′ Cᴿ′ : Ctx}
    {W : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {W′ : Cᴸ′ ⊑ᶜ Cᴿ′}
    {χsᴸ : R.StoreChanges Δᴸ (Δᵉ Cᴸ′)}
    {χsᴿ : R.StoreChanges Δᴿ (Δᵉ Cᴿ′)}
    {M : Term Δᴸ} {N : Term (Δᵉ Cᴸ′)} {A : Ty Δᴸ}
  → (evol : MultiWorldEvolutionᶜ₀ {W = W} {W′ = W′} χsᴸ χsᴿ)
  → ⟨ Δᴸ , Σᴸ , [] ⟩ ⊢ M ⦂ A
  → M —↠[ χsᴸ ] N
  → Cᴸ′ ⊢ N ⦂ R.applyTys χsᴸ A
source-endpoint-typingᶜ₀ {Cᴸ′ = Cᴸ′} {χsᴸ = χsᴸ} evol M⊢ M↠N =
  subst
    (λ Γ → ⟨ Δᵉ Cᴸ′ , Σᵉ Cᴸ′ , Γ ⟩ ⊢
      _ ⦂ R.applyTys χsᴸ _)
    (trans (preservation-term-context-agreesᶜ₀ χsᴸ [])
      (sym (multi-source-term-ctxᶜ₀ evol)))
    (subst
      (λ Σ → ⟨ Δᵉ Cᴸ′ , Σ ,
        Preservation.applyTermCtxs χsᴸ [] ⟩ ⊢
        _ ⦂ R.applyTys χsᴸ _)
      (sym (multi-source-storeᶜ₀ evol))
      (multi-preservation M⊢ M↠N))


target-endpoint-typingᶜ₀ : ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Cᴸ′ Cᴿ′ : Ctx}
    {W : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {W′ : Cᴸ′ ⊑ᶜ Cᴿ′}
    {χsᴸ : R.StoreChanges Δᴸ (Δᵉ Cᴸ′)}
    {χsᴿ : R.StoreChanges Δᴿ (Δᵉ Cᴿ′)}
    {M′ : Term Δᴿ} {N′ : Term (Δᵉ Cᴿ′)} {B : Ty Δᴿ}
  → (evol : MultiWorldEvolutionᶜ₀ {W = W} {W′ = W′} χsᴸ χsᴿ)
  → ⟨ Δᴿ , Σᴿ , [] ⟩ ⊢ M′ ⦂ B
  → M′ —↠[ χsᴿ ] N′
  → Cᴿ′ ⊢ N′ ⦂ R.applyTys χsᴿ B
target-endpoint-typingᶜ₀ {Cᴿ′ = Cᴿ′} {χsᴿ = χsᴿ} evol M⊢ M↠N =
  subst
    (λ Γ → ⟨ Δᵉ Cᴿ′ , Σᵉ Cᴿ′ , Γ ⟩ ⊢
      _ ⦂ R.applyTys χsᴿ _)
    (trans (preservation-term-context-agreesᶜ₀ χsᴿ [])
      (sym (multi-target-term-ctxᶜ₀ evol)))
    (subst
      (λ Σ → ⟨ Δᵉ Cᴿ′ , Σ ,
        Preservation.applyTermCtxs χsᴿ [] ⟩ ⊢
        _ ⦂ R.applyTys χsᴿ _)
      (sym (multi-target-storeᶜ₀ evol))
      (multi-preservation M⊢ M↠N))


module SimulationResultSurfaceᶜ₀
  (FinalTermRelated : ∀ {Cᴸ Cᴿ : Ctx}
    → (W : Cᴸ ⊑ᶜ Cᴿ)
    → {A : Ty (Δᵉ Cᴸ)} {B : Ty (Δᵉ Cᴿ)}
    → A ⊑ᵀ⟨ W ⟩ B
    → Term (Δᵉ Cᴸ)
    → Term (Δᵉ Cᴿ)
    → Set) where

  record SimulationResultᶜ₀
      {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {W : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
      {M : Term Δᴸ} {M′ : Term Δᴿ} {A : Ty Δᴸ} {B : Ty Δᴿ}
      (Cᴸ′ Cᴿ′ : Ctx) {W′ : Cᴸ′ ⊑ᶜ Cᴿ′}
      {χsᴸ : R.StoreChanges Δᴸ (Δᵉ Cᴸ′)}
      {χsᴿ : R.StoreChanges Δᴿ (Δᵉ Cᴿ′)}
      (evol : MultiWorldEvolutionᶜ₀ {W = W} {W′ = W′} χsᴸ χsᴿ)
      (N : Term (Δᵉ Cᴸ′)) (N′ : Term (Δᵉ Cᴿ′)) : Set
      where
    constructor simulation-resultᶜ₀
    field
      source-reduction : M —↠[ χsᴸ ] N
      target-reduction : M′ —↠[ χsᴿ ] N′
      source-initial-typing : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊢ M ⦂ A
      target-initial-typing : ⟨ Δᴿ , Σᴿ , [] ⟩ ⊢ M′ ⦂ B
      final-type-imprecision :
        R.applyTys χsᴸ A ⊑ᵀ⟨ W′ ⟩ R.applyTys χsᴿ B
      final-term-imprecision :
        FinalTermRelated W′ final-type-imprecision N N′

    source-final-typing :
      Cᴸ′ ⊢ N ⦂ R.applyTys χsᴸ A
    source-final-typing =
      source-endpoint-typingᶜ₀ evol source-initial-typing source-reduction

    target-final-typing :
      Cᴿ′ ⊢ N′ ⦂ R.applyTys χsᴿ B
    target-final-typing =
      target-endpoint-typingᶜ₀ evol target-initial-typing target-reduction

    source-store-projection :
      Σᵉ Cᴸ′ ≡ R.applyStores χsᴸ Σᴸ
    source-store-projection = multi-source-storeᶜ₀ evol

    target-store-projection :
      Σᵉ Cᴿ′ ≡ R.applyStores χsᴿ Σᴿ
    target-store-projection = multi-target-storeᶜ₀ evol

    source-context-projection :
      Γᵉ Cᴸ′ ≡ applyTermCtxsᶜ₀ χsᴸ []
    source-context-projection = multi-source-term-ctxᶜ₀ evol

    target-context-projection :
      Γᵉ Cᴿ′ ≡ applyTermCtxsᶜ₀ χsᴿ []
    target-context-projection = multi-target-term-ctxᶜ₀ evol

    source-term-transport : ∀ (P : Term Δᴸ)
      → multi-source-termᶜ₀ evol P ≡ R.applyTerms χsᴸ P
    source-term-transport = multi-source-term-agreesᶜ₀ evol

    target-term-transport : ∀ (P : Term Δᴿ)
      → multi-target-termᶜ₀ evol P ≡ R.applyTerms χsᴿ P
    target-term-transport = multi-target-term-agreesᶜ₀ evol


  data SimulationOutcomeᶜ₀
      {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {W : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ
             ⟨ Δᴿ , Σᴿ , [] ⟩}
      {M : Term Δᴸ} {M′ : Term Δᴿ}
      {A : Ty Δᴸ} {B : Ty Δᴿ} : Set where

    synchronizedᶜ₀ : ∀
        {Cᴸ′ Cᴿ′ : Ctx} {W′ : Cᴸ′ ⊑ᶜ Cᴿ′}
        {χsᴸ : R.StoreChanges Δᴸ (Δᵉ Cᴸ′)}
        {χsᴿ : R.StoreChanges Δᴿ (Δᵉ Cᴿ′)}
        {N : Term (Δᵉ Cᴸ′)} {N′ : Term (Δᵉ Cᴿ′)}
      → (evol : MultiWorldEvolutionᶜ₀
          {W = W} {W′ = W′} χsᴸ χsᴿ)
      → SimulationResultᶜ₀ {W = W} {M = M} {M′ = M′}
          {A = A} {B = B} Cᴸ′ Cᴿ′ evol N N′
      → SimulationOutcomeᶜ₀ {W = W} {M = M} {M′ = M′}
          {A = A} {B = B}

    source-blameᶜ₀ : ∀ {Δᴸ′}
        {χsᴸ : R.StoreChanges Δᴸ Δᴸ′}
      → ⟨ Δᴸ , Σᴸ , [] ⟩ ⊢ M ⦂ A
      → M —↠[ χsᴸ ] blame
      → SimulationOutcomeᶜ₀ {W = W} {M = M} {M′ = M′}
          {A = A} {B = B}

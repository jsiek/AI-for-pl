{-# OPTIONS --safe #-}

module proof.DGG.notes.probes.OpenContextPreservationBoundaryProbe where

-- File Charter:
--   * Checks the smallest open-context preservation boundary needed by the
--     two-Ctx simulation result; it does not assert or reprove preservation.
--   * Takes generalized one-step preservation as an explicit module input and
--     derives generalized multi-step and endpoint preservation mechanically.
--   * Isolates the missing trusted theorem from the already checked world
--     evolution, store, context, and sequence transport surfaces.

open import Relation.Binary.PropositionalEquality using (sym; subst)

open import Types using (Ty)
open import TyStore using (TyStore)
open import TermCtx using (TermCtx)
open import CastTerms using
  (Ctx; ⟨_,_,_⟩; Δᵉ; Σᵉ; Γᵉ; Term; _⊢_⦂_)
import Reduction as R
open import Reduction using (_—→[_]_; _—↠[_]_; ↠-refl; ↠-step)
open import proof.DGG.notes.probes.TwoCtxWorldSkeletonProbe
open import proof.DGG.notes.probes.TwoCtxWorldEvolutionProbe using
  (applyTermCtxᶜ₀)
open import proof.DGG.notes.probes.TwoCtxWorldEvolutionSequenceProbe


module OpenPreservationConsequencesᶜ₀
  (open-preservation : ∀ {Δ Δ′} {Σ : TyStore Δ} {Γ : TermCtx Δ}
      {M : Term Δ} {N : Term Δ′} {A : Ty Δ}
      {χ : R.StoreChange Δ Δ′}
    → ⟨ Δ , Σ , Γ ⟩ ⊢ M ⦂ A
    → M —→[ χ ] N
    → ⟨ Δ′ , R.applyStore χ Σ , applyTermCtxᶜ₀ χ Γ ⟩
        ⊢ N ⦂ R.applyTy χ A)
  where

  open-multi-preservationᶜ₀ : ∀ {Δ Δ′} {Σ : TyStore Δ}
      {Γ : TermCtx Δ} {M : Term Δ} {N : Term Δ′}
      {A : Ty Δ} {χs : R.StoreChanges Δ Δ′}
    → ⟨ Δ , Σ , Γ ⟩ ⊢ M ⦂ A
    → M —↠[ χs ] N
    → ⟨ Δ′ , R.applyStores χs Σ , applyTermCtxsᶜ₀ χs Γ ⟩
        ⊢ N ⦂ R.applyTys χs A
  open-multi-preservationᶜ₀ M⊢ ↠-refl = M⊢
  open-multi-preservationᶜ₀ M⊢ (↠-step red reds) =
    open-multi-preservationᶜ₀ (open-preservation M⊢ red) reds


  source-open-endpoint-typingᶜ₀ : ∀
      {Cᴸ Cᴿ Cᴸ′ Cᴿ′ : Ctx}
      {W : Cᴸ ⊑ᶜ₀ Cᴿ} {W′ : Cᴸ′ ⊑ᶜ₀ Cᴿ′}
      {χsᴸ : R.StoreChanges (Δᵉ Cᴸ) (Δᵉ Cᴸ′)}
      {χsᴿ : R.StoreChanges (Δᵉ Cᴿ) (Δᵉ Cᴿ′)}
      {M : Term (Δᵉ Cᴸ)} {N : Term (Δᵉ Cᴸ′)}
      {A : Ty (Δᵉ Cᴸ)}
    → (evol : MultiWorldEvolutionᶜ₀
        {W = W} {W′ = W′} χsᴸ χsᴿ)
    → Cᴸ ⊢ M ⦂ A
    → M —↠[ χsᴸ ] N
    → Cᴸ′ ⊢ N ⦂ R.applyTys χsᴸ A
  source-open-endpoint-typingᶜ₀
      {Cᴸ = Cᴸ} {Cᴸ′ = Cᴸ′} {χsᴸ = χsᴸ} evol M⊢ M↠N =
    subst
      (λ Γ → ⟨ Δᵉ Cᴸ′ , Σᵉ Cᴸ′ , Γ ⟩ ⊢
        _ ⦂ R.applyTys χsᴸ _)
      (sym (multi-source-term-ctxᶜ₀ evol))
      (subst
        (λ Σ → ⟨ Δᵉ Cᴸ′ , Σ , applyTermCtxsᶜ₀ χsᴸ (Γᵉ Cᴸ) ⟩
          ⊢ _ ⦂ R.applyTys χsᴸ _)
        (sym (multi-source-storeᶜ₀ evol))
        (open-multi-preservationᶜ₀ M⊢ M↠N))


  target-open-endpoint-typingᶜ₀ : ∀
      {Cᴸ Cᴿ Cᴸ′ Cᴿ′ : Ctx}
      {W : Cᴸ ⊑ᶜ₀ Cᴿ} {W′ : Cᴸ′ ⊑ᶜ₀ Cᴿ′}
      {χsᴸ : R.StoreChanges (Δᵉ Cᴸ) (Δᵉ Cᴸ′)}
      {χsᴿ : R.StoreChanges (Δᵉ Cᴿ) (Δᵉ Cᴿ′)}
      {M′ : Term (Δᵉ Cᴿ)} {N′ : Term (Δᵉ Cᴿ′)}
      {B : Ty (Δᵉ Cᴿ)}
    → (evol : MultiWorldEvolutionᶜ₀
        {W = W} {W′ = W′} χsᴸ χsᴿ)
    → Cᴿ ⊢ M′ ⦂ B
    → M′ —↠[ χsᴿ ] N′
    → Cᴿ′ ⊢ N′ ⦂ R.applyTys χsᴿ B
  target-open-endpoint-typingᶜ₀
      {Cᴿ = Cᴿ} {Cᴿ′ = Cᴿ′} {χsᴿ = χsᴿ} evol M⊢ M↠N =
    subst
      (λ Γ → ⟨ Δᵉ Cᴿ′ , Σᵉ Cᴿ′ , Γ ⟩ ⊢
        _ ⦂ R.applyTys χsᴿ _)
      (sym (multi-target-term-ctxᶜ₀ evol))
      (subst
        (λ Σ → ⟨ Δᵉ Cᴿ′ , Σ , applyTermCtxsᶜ₀ χsᴿ (Γᵉ Cᴿ) ⟩
          ⊢ _ ⦂ R.applyTys χsᴿ _)
        (sym (multi-target-storeᶜ₀ evol))
        (open-multi-preservationᶜ₀ M⊢ M↠N))


-- The missing input generalizes the existing one-step `preservation` only in
-- its term context.  Its proof needs open versions of `change-typing`,
-- `pure-preservation`, and `reveal-zero-typing`.  The reusable dependencies
-- already accept arbitrary contexts: `typing-shiftᵗ-bind`,
-- `typing-single-subst`, conversion/store transport, and the allocation type
-- equations.  Multi-step and two-Ctx endpoint preservation above then follow
-- without any further operational or world law.

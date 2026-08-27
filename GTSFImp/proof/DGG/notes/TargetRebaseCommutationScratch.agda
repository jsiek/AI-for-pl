{-# OPTIONS --safe #-}

module proof.DGG.notes.TargetRebaseCommutationScratch where

-- Probe for the chronological target-bind scope stack.  A root target bind is
-- admitted only before source rebasing starts.  Each direct source rebase then
-- pushes the exact before/after square onto the scope derivation.

import Data.Fin as Fin
import Data.Nat as Nat
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types using (Ty; TyVar; ＇_)
open import Consistency using (_↪ᵗ_; toRenameᵗ; wk↪ᵗ)
open import TyStore using (TyStore; lookupStore)
open import TermCtx using (TermCtx; ⇑ᶜ)
open import CastTerms using (Ctx; ⟨_,_,_⟩)

open import proof.DGG.World
open import proof.DGG.SourceRebase


data TargetBindStack : ∀
    {Δᴸ Δᴿ Δᴿ⁺}
    {Σᴸ : TyStore Δᴸ}
    {Σᴿ : TyStore Δᴿ} {Σᴿ⁺ : TyStore Δᴿ⁺}
    {Γᴸ : TermCtx Δᴸ}
    {Γᴿ : TermCtx Δᴿ} {Γᴿ⁺ : TermCtx Δᴿ⁺}
  → (ρ : Δᴿ ↪ᵗ Δᴿ⁺)
  → (γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩)
  → (γ⁺ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩)
  → Set where

  target-stack-root : ∀
      {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {Γᴿ⁺ : TermCtx (Nat.suc Δᴿ)} {C : Ty Δᴿ}
      {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    → sourceRebaseCountᶜ γ ≡ Nat.zero
    → (fresh : RightBindFreshᶜ γ C)
    → (eqᴿ : Γᴿ⁺ ≡ ⇑ᶜ Γᴿ)
    → TargetBindStack wk↪ᵗ γ
        (γ ▻ᶜ bind-right-changeᶜ C fresh eqᴿ)

  target-stack-rebase : ∀
      {Δᴸ Δᴿ Δᴿ⁺}
      {Σᴸ : TyStore Δᴸ}
      {Σᴿ : TyStore Δᴿ} {Σᴿ⁺ : TyStore Δᴿ⁺}
      {Γᴸ : TermCtx Δᴸ}
      {Γᴿ : TermCtx Δᴿ} {Γᴿ⁺ : TermCtx Δᴿ⁺}
      {ρ : Δᴿ ↪ᵗ Δᴿ⁺}
      {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {γ⁺ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
        ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩}
      {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
      {Xᴿ⁺ : TyVar Δᴿ⁺}
    → (plan : TargetBindStack ρ γ γ⁺)
    → (eq-Xᴿ : toRenameᵗ ρ Xᴿ ≡ Xᴿ⁺)
    → (ok : CanRebaseSourceᵗ
        (ηᴸᶜ γ) Xᴸ (toRenameᵗ (ηᴿᶜ γ) Xᴿ))
    → (represented :
        (＇ Xᴸ) ⊑ᵀ⟨ γ ⟩ lookupStore Σᴿ Xᴿ)
    → (ok⁺ : CanRebaseSourceᵗ
        (ηᴸᶜ γ⁺) Xᴸ (toRenameᵗ (ηᴿᶜ γ⁺) Xᴿ⁺))
    → (represented⁺ :
        (＇ Xᴸ) ⊑ᵀ⟨ γ⁺ ⟩ lookupStore Σᴿ⁺ Xᴿ⁺)
    → TargetBindStack ρ
        (γ ▻ᶜ rebase-source-changeᶜ
          Xᴸ Xᴿ ok represented)
        (γ⁺ ▻ᶜ rebase-source-changeᶜ
          Xᴸ Xᴿ⁺ ok⁺ represented⁺)


-- Matching the direct SourceRebase proof against the top stack frame recovers
-- the preceding plan and the output-side rebase without proof equality.
target-stack-pop : ∀
    {Δᴸ Δᴿ Δᴿ⁺}
    {Σᴸ : TyStore Δᴸ}
    {Σᴿ : TyStore Δᴿ} {Σᴿ⁺ : TyStore Δᴿ⁺}
    {Γᴸ : TermCtx Δᴸ}
    {Γᴿ : TermCtx Δᴿ} {Γᴿ⁺ : TermCtx Δᴿ⁺}
    {ρ : Δᴿ ↪ᵗ Δᴿ⁺}
    {γ γᵖ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → SourceRebaseᶜ γᵖ γ Xᴸ Xᴿ
  → (plan : TargetBindStack ρ γ γ⁺)
  → Σ[ γᵖ⁺ ∈ (⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
        ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩) ]
      TargetBindStack ρ γᵖ γᵖ⁺
    × SourceRebaseᶜ γᵖ⁺ γ⁺ Xᴸ (toRenameᵗ ρ Xᴿ)
target-stack-pop rebase (target-stack-root no-rebase fresh eqᴿ) =
  ⊥-elim (source-rebase-count≢zero rebase no-rebase)
target-stack-pop
    (source-rebase-now ok represented)
    (target-stack-rebase plan refl .ok .represented ok⁺ represented⁺) =
  _ , plan , source-rebase-now ok⁺ represented⁺

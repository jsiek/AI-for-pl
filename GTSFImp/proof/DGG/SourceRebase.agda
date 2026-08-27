{-# OPTIONS --safe #-}

module proof.DGG.SourceRebase where

-- File Charter:
--   * Defines the source-rebase relation between two worlds with the same
--     endpoint contexts.
--   * Records a direct source rebase and closes that rebase under matching
--     endpoint-indexed world evolution.
--   * Keeps transported pivot indices in constructor form by recording their
--     executable-renaming equations as premises.
--   * Exports no compatibility equality or action wrapper; depends only on
--     World and WorldEvolution.

open import Data.Nat using (zero; suc)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; cong; sym; trans)

open import Types using (TyVar; ＇_)
open import Consistency using (toRenameᵗ)
open import TyStore using (lookupStore)
open import CastTerms using (Ctx; Δᵉ; Σᵉ)
import Reduction as R

open import proof.DGG.World
open import proof.DGG.WorldEvolution


data SourceRebaseᶜ : ∀ {Γᴸ Γᴿ}
    → Γᴸ ⊑ᶜ Γᴿ
    → Γᴸ ⊑ᶜ Γᴿ
    → TyVar (Δᵉ Γᴸ)
    → TyVar (Δᵉ Γᴿ)
    → Set where

  source-rebase-now : ∀ {Γᴸ Γᴿ}
      {γ : Γᴸ ⊑ᶜ Γᴿ} {Xᴸ Xᴿ}
      (ok : CanRebaseSourceᵗ
        (ηᴸᶜ γ) Xᴸ (toRenameᵗ (ηᴿᶜ γ) Xᴿ))
      (represented :
        (＇ Xᴸ) ⊑ᵀ⟨ γ ⟩ lookupStore (Σᵉ Γᴿ) Xᴿ)
    → SourceRebaseᶜ γ
        (γ ▻ᶜ rebase-source-changeᶜ
          Xᴸ Xᴿ ok represented)
        Xᴸ Xᴿ

  source-rebase-step : ∀
      {Γᴸ Γᴿ Γᴸ⁺ Γᴿ⁺ : Ctx}
      {γ γᵖ : Γᴸ ⊑ᶜ Γᴿ}
      {γ⁺ γᵖ⁺ : Γᴸ⁺ ⊑ᶜ Γᴿ⁺}
      {stepᴸ : CtxChange Γᴸ Γᴸ⁺}
      {stepᴿ : CtxChange Γᴿ Γᴿ⁺}
      {Xᴸ Xᴿ Xᴸ⁺ Xᴿ⁺}
    → SourceRebaseᶜ γ γᵖ Xᴸ Xᴿ
    → WorldEvolution {W = γ} {W′ = γ⁺} stepᴸ stepᴿ
    → WorldEvolution {W = γᵖ} {W′ = γᵖ⁺} stepᴸ stepᴿ
    → R.applyVar (storeChange stepᴸ) Xᴸ ≡ Xᴸ⁺
    → R.applyVar (storeChange stepᴿ) Xᴿ ≡ Xᴿ⁺
    → SourceRebaseᶜ γ⁺ γᵖ⁺ Xᴸ⁺ Xᴿ⁺


source-rebase-center : ∀ {Γᴸ Γᴿ}
    {γ γᵖ : Γᴸ ⊑ᶜ Γᴿ} {Xᴸ Xᴿ}
  → SourceRebaseᶜ γ γᵖ Xᴸ Xᴿ
  → centerᶜ γ ≡ centerᶜ γᵖ
source-rebase-center (source-rebase-now ok represented) = refl
source-rebase-center
    (source-rebase-step rebase evolution-keep evolution-keep eqᴸ eqᴿ) =
  source-rebase-center rebase
source-rebase-center
    (source-rebase-step rebase
      (evolution-bind-left eqᴸ)
      (evolution-bind-left eqᴸ′) Xᴸ≡ Xᴿ≡) =
  cong suc (source-rebase-center rebase)
source-rebase-center
    (source-rebase-step rebase
      (evolution-bind-right fresh eqᴿ)
      (evolution-bind-right fresh′ eqᴿ′) Xᴸ≡ Xᴿ≡) =
  cong suc (source-rebase-center rebase)
source-rebase-center
    (source-rebase-step rebase
      (evolution-bind-both represented eqᴸ eqᴿ)
      (evolution-bind-both represented′ eqᴸ′ eqᴿ′) Xᴸ≡ Xᴿ≡) =
  cong suc (source-rebase-center rebase)
source-rebase-center
    (source-rebase-step rebase
      (evolution-bind-both represented eqᴸ eqᴿ)
      (evolution-bind-both-star represented′ A≢★ eqᴸ′ eqᴿ′)
      Xᴸ≡ Xᴿ≡) =
  cong suc (source-rebase-center rebase)
source-rebase-center
    (source-rebase-step rebase
      (evolution-bind-both-star represented A≢★ eqᴸ eqᴿ)
      (evolution-bind-both represented′ eqᴸ′ eqᴿ′) Xᴸ≡ Xᴿ≡) =
  cong suc (source-rebase-center rebase)
source-rebase-center
    (source-rebase-step rebase
      (evolution-bind-both-star represented A≢★ eqᴸ eqᴿ)
      (evolution-bind-both-star represented′ A≢★′ eqᴸ′ eqᴿ′)
      Xᴸ≡ Xᴿ≡) =
  cong suc (source-rebase-center rebase)


source-rebase-count : ∀ {Γᴸ Γᴿ}
    {γ γᵖ : Γᴸ ⊑ᶜ Γᴿ} {Xᴸ Xᴿ}
  → SourceRebaseᶜ γ γᵖ Xᴸ Xᴿ
  → sourceRebaseCountᶜ γᵖ ≡ suc (sourceRebaseCountᶜ γ)
source-rebase-count (source-rebase-now ok represented) = refl
source-rebase-count
    (source-rebase-step rebase evolution-keep evolution-keep eqᴸ eqᴿ) =
  source-rebase-count rebase
source-rebase-count
    (source-rebase-step rebase
      (evolution-bind-left eqᴸ)
      (evolution-bind-left eqᴸ′) Xᴸ≡ Xᴿ≡) =
  source-rebase-count rebase
source-rebase-count
    (source-rebase-step rebase
      (evolution-bind-right fresh eqᴿ)
      (evolution-bind-right fresh′ eqᴿ′) Xᴸ≡ Xᴿ≡) =
  source-rebase-count rebase
source-rebase-count
    (source-rebase-step rebase
      (evolution-bind-both represented eqᴸ eqᴿ)
      (evolution-bind-both represented′ eqᴸ′ eqᴿ′) Xᴸ≡ Xᴿ≡) =
  source-rebase-count rebase
source-rebase-count
    (source-rebase-step rebase
      (evolution-bind-both represented eqᴸ eqᴿ)
      (evolution-bind-both-star represented′ A≢★ eqᴸ′ eqᴿ′)
      Xᴸ≡ Xᴿ≡) =
  source-rebase-count rebase
source-rebase-count
    (source-rebase-step rebase
      (evolution-bind-both-star represented A≢★ eqᴸ eqᴿ)
      (evolution-bind-both represented′ eqᴸ′ eqᴿ′) Xᴸ≡ Xᴿ≡) =
  source-rebase-count rebase
source-rebase-count
    (source-rebase-step rebase
      (evolution-bind-both-star represented A≢★ eqᴸ eqᴿ)
      (evolution-bind-both-star represented′ A≢★′ eqᴸ′ eqᴿ′)
      Xᴸ≡ Xᴿ≡) =
  source-rebase-count rebase


source-rebase-count≢zero : ∀ {Γᴸ Γᴿ}
    {γ γᵖ : Γᴸ ⊑ᶜ Γᴿ} {Xᴸ Xᴿ}
  → SourceRebaseᶜ γ γᵖ Xᴸ Xᴿ
  → sourceRebaseCountᶜ γᵖ ≢ zero
source-rebase-count≢zero rebase eq
    with trans (sym (source-rebase-count rebase)) eq
source-rebase-count≢zero rebase eq | ()

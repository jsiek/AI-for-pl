{-# OPTIONS --safe #-}

module proof.DGG.notes.AlignmentOnlyRebaseInvariantProbe where

-- File Charter:
--   * Finds the smallest checked semantic payload for an alignment-only
--     source rebase: an actual paired reveal or conceal boundary, checked
--     using the post-update source injection.
--   * Instantiates that payload at TargetIdentityReveal checkpoint 3.
--   * Proves that the raw allocation world has the direct world invariants,
--     while its trusted alpha-aligned successor cannot have them: unmatched
--     target beta still aliases the newly aligned target alpha.
--   * Consequently separates the open-frame scan from the stronger
--     source-rebase-count gate used by DirectWorldInvariants.

open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ-syntax; _,_)
open import Data.Sum using (inj₁; inj₂)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Types using (Ty; TyVar; ★; ＇_; renameᵗ)
open import TyStore using (lookupStore)
open import Conversion using
  (Conv↑; Conv↓; _⊢↑[_⦂_]_; _⊢↓[_⦂_]_)
open import Imprecision using (X⊑X; X⊑★; _⊢_⊑_)
open import CastTerms using (Ctx; Δᵉ; Σᵉ)
open import proof.DGG.ConversionPivotAlignment using
  (revealGeneratorPosition; concealGeneratorPosition)
open import proof.DGG.World
open import proof.DGG.WorldInvariants
import proof.DGG.Examples.TargetIdentityReveal as TIR


------------------------------------------------------------------------
-- Exact proposed payload for an alignment-only source rebase
------------------------------------------------------------------------

-- The payload is constructed before the WorldChange, so the comparison that
-- will become `Rᴸ ⊑ᵀ⟨ γ′ ⟩ Rᴿ` is written directly using the
-- post-update source injection.  This avoids an extensional invariant field
-- and avoids referring recursively to the world under construction.

data AlignmentBoundaryᶜ {Γᴸ Γᴿ : Ctx} (γ : Γᴸ ⊑ᶜ Γᴿ)
    (Xᴸ : TyVar (Δᵉ Γᴸ)) (Xᴿ : TyVar (Δᵉ Γᴿ))
    (update : PivotUpdateᵗ (ηᴸᶜ γ) Xᴸ (toRenameⁱ (ηᴿᶜ γ) Xᴿ)) : Set where

  paired-reveal-alignmentᶜ : ∀ {A A′ B B′ Rᴸ Rᴿ}
      {c : Conv↑ (Δᵉ Γᴸ) A B}
      {c′ : Conv↑ (Δᵉ Γᴿ) A′ B′}
    → (c⊢ : Σᵉ Γᴸ ⊢↑[ Xᴸ ⦂ Rᴸ ] c)
    → (c′⊢ : Σᵉ Γᴿ ⊢↑[ Xᴿ ⦂ Rᴿ ] c′)
    → revealGeneratorPosition c⊢ ≡ revealGeneratorPosition c′⊢
    → marksᶜ γ ⊢
        renameᵗ (toRenameⁱ (pivot-afterᵗ update)) Rᴸ
          ⊑ renameᵗ (toRenameⁱ (ηᴿᶜ γ)) Rᴿ
    → AlignmentBoundaryᶜ γ Xᴸ Xᴿ update

  paired-conceal-alignmentᶜ : ∀ {A A′ B B′ Rᴸ Rᴿ}
      {c : Conv↓ (Δᵉ Γᴸ) A B}
      {c′ : Conv↓ (Δᵉ Γᴿ) A′ B′}
    → (c⊢ : Σᵉ Γᴸ ⊢↓[ Xᴸ ⦂ Rᴸ ] c)
    → (c′⊢ : Σᵉ Γᴿ ⊢↓[ Xᴿ ⦂ Rᴿ ] c′)
    → concealGeneratorPosition c⊢ ≡ concealGeneratorPosition c′⊢
    → marksᶜ γ ⊢
        renameᵗ (toRenameⁱ (pivot-afterᵗ update)) Rᴸ
          ⊑ renameᵗ (toRenameⁱ (ηᴿᶜ γ)) Rᴿ
    → AlignmentBoundaryᶜ γ Xᴸ Xᴿ update


data SourceRebaseRoleᶜ {Γᴸ Γᴿ : Ctx} (γ : Γᴸ ⊑ᶜ Γᴿ)
    (Xᴸ : TyVar (Δᵉ Γᴸ)) (Xᴿ : TyVar (Δᵉ Γᴿ))
    (update : PivotUpdateᵗ (ηᴸᶜ γ) Xᴸ (toRenameⁱ (ηᴿᶜ γ) Xᴿ)) : Set where
  open-frameᶜ : SourceRebaseRoleᶜ γ Xᴸ Xᴿ update
  alignment-onlyᶜ : AlignmentBoundaryᶜ γ Xᴸ Xᴿ update
    → SourceRebaseRoleᶜ γ Xᴸ Xᴿ update


role-open-count : ∀ {Γᴸ Γᴿ : Ctx} {γ : Γᴸ ⊑ᶜ Γᴿ}
    {Xᴸ : TyVar (Δᵉ Γᴸ)} {Xᴿ : TyVar (Δᵉ Γᴿ)} {update}
  → SourceRebaseRoleᶜ γ Xᴸ Xᴿ update
  → ℕ
role-open-count open-frameᶜ = 1
role-open-count (alignment-onlyᶜ boundary) = 0


------------------------------------------------------------------------
-- Trusted TargetIdentityReveal checkpoint-3 payload
------------------------------------------------------------------------

checkpoint₃-alpha-boundary :
  AlignmentBoundaryᶜ TIR.checkpoint₃-allocation-world Fin.zero
    (Fin.suc Fin.zero) TIR.checkpoint₃-alpha-ok
checkpoint₃-alpha-boundary =
  paired-reveal-alignmentᶜ
    TIR.checkpoint₃-source-reveal⊢
    TIR.checkpoint₁-alpha-reveal⊢
    refl
    Imprecision.ι⊑★


checkpoint₃-alpha-role : SourceRebaseRoleᶜ
  TIR.checkpoint₃-allocation-world Fin.zero (Fin.suc Fin.zero)
  TIR.checkpoint₃-alpha-ok
checkpoint₃-alpha-role = alignment-onlyᶜ checkpoint₃-alpha-boundary


checkpoint₃-alpha-opens-no-frame :
  role-open-count checkpoint₃-alpha-role ≡ 0
checkpoint₃-alpha-opens-no-frame = refl


-- These are the local post-update facts needed by the paired reveal.  They
-- are available without postulating a complete world invariant.

checkpoint₃-alpha-aligned :
  toRenameⁱ (ηᴸᶜ TIR.checkpoint₃-world) Fin.zero ≡
    toRenameⁱ (ηᴿᶜ TIR.checkpoint₃-world) (Fin.suc Fin.zero)
checkpoint₃-alpha-aligned = pivot-alignedᵗ TIR.checkpoint₃-alpha-ok


checkpoint₃-alpha-representations-imprecise :
  TIR.ℕᵗ ⊑ᵀ⟨ TIR.checkpoint₃-world ⟩ ★
checkpoint₃-alpha-representations-imprecise = Imprecision.ι⊑★


------------------------------------------------------------------------
-- DirectWorldInvariants obstruction
------------------------------------------------------------------------

-- Before the alignment-only update, this is an ordinary zero-rebase world
-- and the live structural theorem applies.

checkpoint₃-allocation-direct :
  DirectWorldInvariantsᶜ TIR.checkpoint₃-allocation-world
checkpoint₃-allocation-direct =
  directInvariantsᶜ TIR.checkpoint₃-allocation-world refl


-- After alpha is paired, target beta remains unmatched.  Its direct store
-- entry is the variable alpha, but alpha now has source X as an occupant.
-- This contradicts both alternatives of unmatchedTargetsDynamicᶜ.

checkpoint₃-alpha-not-direct :
  DirectWorldInvariantsᶜ TIR.checkpoint₃-world → ⊥
checkpoint₃-alpha-not-direct inv
    with unmatchedTargetsDynamicᶜ inv Fin.zero (λ { Fin.zero () })
checkpoint₃-alpha-not-direct inv | inj₁ ()
checkpoint₃-alpha-not-direct inv |
    inj₂ (Fin.zero , () , alias-unmatched)
checkpoint₃-alpha-not-direct inv |
    inj₂ (Fin.suc Fin.zero , refl , alias-unmatched) =
  alias-unmatched Fin.zero refl
checkpoint₃-alpha-not-direct inv |
    inj₂ (Fin.suc (Fin.suc ()) , entry , alias-unmatched)

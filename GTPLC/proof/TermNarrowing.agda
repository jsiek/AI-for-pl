module proof.TermNarrowing where

-- File Charter:
--   * Derives paired narrowing-cast and widening-cast term rules.
--   * Builds each rule from the one-sided cast constructors.
--   * Shares the relocation component across each paired cast square.
--   * Checks the left and right narrowing equations independently.

open import Data.Product using (_,_)
open import Types
open import TyStore
open import Ctx
open import Coercions
open import Terms
open import NarrowWiden
open import TypeRelocate
open import FactoredTypeNarrowing
open import ImprecisionTheorems using (dualʷ; _⨟ⁿ_)
open import EnvironmentNarrowing
open import TermNarrowing

------------------------------------------------------------------------
-- Paired narrowing casts
------------------------------------------------------------------------

castⁿ⊒castⁿ : ∀ {Δᴸ Δᴿ Σᴸ Σᴿ Γᴸ Γᴿ M M′ A A′}
    {C C′ D D′ s t}
    {Φ : ImpCtx Δᴸ Δᴿ}
    {ρ : NarrowingEnv Φ {Σᴸ} {Σᴿ} {Γᴸ} {Γᴿ}}
    {pᴸ : ρ ⊢ᴸⁿ A ⊒ C}
    {qᴸ : ρ ⊢ᴸⁿ D ⊒ C}
    {relocation : Φ ⊢ C ≈ C′}
    {pᴿ : ρ ⊢ᴿⁿ C′ ⊒ A′}
    {qᴿ : ρ ⊢ᴿⁿ C′ ⊒ D′}
    {s⦂ : ρ ⊢ᴸⁿ s ⦂ A ⊒ D}
    {t⦂ : ρ ⊢ᴿⁿ t ⦂ A′ ⊒ D′}
  → ρ ⊢ᴺ M ⊒ M′ ∶ (pᴸ ⨟ᶠ relocation ⨟ᶠ pᴿ)
  → ((s , s⦂) ⨟ⁿ qᴸ) ≐ⁿ pᴸ
  → (pᴿ ⨟ⁿ (t , t⦂)) ≐ⁿ qᴿ
    --------------------------------
  → ρ ⊢ᴺ M ⟨ s ⟩ ⊒ M′ ⟨ t ⟩
      ∶ (qᴸ ⨟ᶠ relocation ⨟ᶠ qᴿ)
castⁿ⊒castⁿ {s⦂ = s⦂} {t⦂ = t⦂}
    M⊒M′ left-eq right-eq =
  castⁿ⊒ {s⦂ = s⦂}
    (⊒castⁿ {t⦂ = t⦂} M⊒M′ right-eq)
    left-eq

------------------------------------------------------------------------
-- Paired widening casts
------------------------------------------------------------------------

castʷ⊒castʷ : ∀ {Δᴸ Δᴿ Σᴸ Σᴿ Γᴸ Γᴿ M M′ A A′}
    {C C′ D D′ u u′}
    {Φ : ImpCtx Δᴸ Δᴿ}
    {ρ : NarrowingEnv Φ {Σᴸ} {Σᴿ} {Γᴸ} {Γᴿ}}
    {pᴸ : ρ ⊢ᴸⁿ A ⊒ C}
    {qᴸ : ρ ⊢ᴸⁿ D ⊒ C}
    {relocation : Φ ⊢ C ≈ C′}
    {pᴿ : ρ ⊢ᴿⁿ C′ ⊒ A′}
    {qᴿ : ρ ⊢ᴿⁿ C′ ⊒ D′}
    {u⦂ : ρ ⊢ᴸʷ u ⦂ A ⊑ D}
    {u′⦂ : ρ ⊢ᴿʷ u′ ⦂ A′ ⊑ D′}
  → ρ ⊢ᴺ M ⊒ M′ ∶ (pᴸ ⨟ᶠ relocation ⨟ᶠ pᴿ)
  → (dualʷ (u , u⦂) ⨟ⁿ pᴸ) ≐ⁿ qᴸ
  → (qᴿ ⨟ⁿ dualʷ (u′ , u′⦂)) ≐ⁿ pᴿ
    --------------------------------
  → ρ ⊢ᴺ M ⟨ u ⟩ ⊒ M′ ⟨ u′ ⟩
      ∶ (qᴸ ⨟ᶠ relocation ⨟ᶠ qᴿ)
castʷ⊒castʷ {u⦂ = u⦂} {u′⦂ = u′⦂}
    M⊒M′ left-eq right-eq =
  ⊒castʷ {t⦂ = u′⦂}
    (castʷ⊒ {s⦂ = u⦂} M⊒M′ left-eq)
    right-eq

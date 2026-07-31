module proof.TermNarrowing where

-- File Charter:
--   * Derives paired narrowing-cast and widening-cast term rules.
--   * Builds each rule from the one-sided cast constructors.
--   * Uses an explicit intermediate type narrowing.
--   * Checks the four outer endpoints with the paired endpoint witness.

open import Types
open import TyStore
open import Ctx
open import Coercions
open import Terms
open import TypeNarrow
open import NarrowWiden
open import EnvironmentNarrowing
open import TermNarrowing

------------------------------------------------------------------------
-- Paired narrowing casts
------------------------------------------------------------------------

castⁿ⊒castⁿ : ∀ {Δᴸ Δᴿ Σᴸ Σᴿ Γᴸ Γᴿ M M′ A A′}
    {D D′ s t μ μ′}
    {Φ : ImpCtx Δᴸ Δᴿ}
    {ρ : NarrowingEnv Φ {Σᴸ} {Σᴿ} {Γᴸ} {Γᴿ}}
    {p : ρ ⊢ᵀ A ⊒ A′}
    {q : ρ ⊢ᵀ D ⊒ D′}
    {r : ρ ⊢ᵀ A ⊒ D′}
    {s⦂ : μ ∣ ρ ⊢ᴸ s ⦂ A ⊒ D}
    {t⦂ : μ′ ∣ ρ ⊢ᴿ t ⦂ A′ ⊒ D′}
  → ρ ⊢ᴺ M ⊒ M′ ∶ p
  → s⦂ ⨟ q ≈ p ⨟ t⦂
    --------------------------------
  → ρ ⊢ᴺ M ⟨ s ⟩ ⊒ M′ ⟨ t ⟩ ∶ q
castⁿ⊒castⁿ {r = r} {s⦂ = s⦂} {t⦂ = t⦂} M⊒M′ square =
  castⁿ⊒ {s⦂ = s⦂}
    (⊒castⁿ {t⦂ = t⦂} M⊒M′ (endpointsʳⁿ {q = r}))
    (endpointsˡⁿ {p = r})

------------------------------------------------------------------------
-- Paired widening casts
------------------------------------------------------------------------

castʷ⊒castʷ : ∀ {Δᴸ Δᴿ Σᴸ Σᴿ Γᴸ Γᴿ M M′ A A′}
    {D D′ u u′ μ μ′}
    {Φ : ImpCtx Δᴸ Δᴿ}
    {ρ : NarrowingEnv Φ {Σᴸ} {Σᴿ} {Γᴸ} {Γᴿ}}
    {q : ρ ⊢ᵀ A ⊒ A′}
    {p : ρ ⊢ᵀ D ⊒ D′}
    {r : ρ ⊢ᵀ A ⊒ D′}
    {u⦂ : μ ∣ ρ ⊢ᴸ u ⦂ A ⊑ D}
    {u′⦂ : μ′ ∣ ρ ⊢ᴿ u′ ⦂ A′ ⊑ D′}
  → ρ ⊢ᴺ M ⊒ M′ ∶ q
  → u⦂ ⨟ q ≈ p ⨟ u′⦂
    --------------------------------
  → ρ ⊢ᴺ M ⟨ u ⟩ ⊒ M′ ⟨ u′ ⟩ ∶ p
castʷ⊒castʷ {r = r} {u⦂ = u⦂} {u′⦂ = u′⦂}
    M⊒M′ square =
  castʷ⊒ {s⦂ = u⦂}
    (⊒castʷ {t⦂ = u′⦂} M⊒M′ (endpointsʳʷ {q = r}))
    (endpointsˡʷ {p = r})

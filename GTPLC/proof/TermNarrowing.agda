module proof.TermNarrowing where

-- File Charter:
--   * Derives paired narrowing-cast and widening-cast term rules.
--   * Builds each rule from the one-sided cast constructors.
--   * Uses normalized factored composition as the intermediate narrowing.
--   * Checks paired cast squares by equality of normalized coercions.

open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (refl; sym)

open import Types
open import TyStore
open import Ctx
open import Coercions
open import Terms
open import NarrowWiden
open import TypeRelocate
open import FactoredTypeNarrowing
open import ImprecisionTheorems using (dualʷ)
open import EnvironmentNarrowing
open import TermNarrowing

------------------------------------------------------------------------
-- Paired narrowing casts
------------------------------------------------------------------------

castⁿ⊒castⁿ : ∀ {Δᴸ Δᴿ Σᴸ Σᴿ Γᴸ Γᴿ M M′ A A′}
    {D D′ s t}
    {Φ : ImpCtx Δᴸ Δᴿ}
    {ρ : NarrowingEnv Φ {Σᴸ} {Σᴿ} {Γᴸ} {Γᴿ}}
    {p : ρ ⊢ᵀ A ⊒ A′}
    {q : ρ ⊢ᵀ D ⊒ D′}
    {s⦂ : ρ ⊢ᴸⁿ s ⦂ A ⊒ D}
    {t⦂ : ρ ⊢ᴿⁿ t ⦂ A′ ⊒ D′}
  → ρ ⊢ᴺ M ⊒ M′ ∶ p
  → (s , s⦂) ⨟ⁿᶠ q ≐ᶠ p ⨟ᶠⁿ (t , t⦂)
    --------------------------------
  → ρ ⊢ᴺ M ⟨ s ⟩ ⊒ M′ ⟨ t ⟩ ∶ q
castⁿ⊒castⁿ {p = p} {q = q} {s⦂ = s⦂} {t⦂ = t⦂}
    M⊒M′ square =
  castⁿ⊒ {p = p ⨟ᶠⁿ (_ , t⦂)} {q = q} {s⦂ = s⦂}
    (⊒castⁿ {p = p} {q = p ⨟ᶠⁿ (_ , t⦂)}
      {t⦂ = t⦂} M⊒M′ (refl , refl))
    square

------------------------------------------------------------------------
-- Paired widening casts
------------------------------------------------------------------------

castʷ⊒castʷ : ∀ {Δᴸ Δᴿ Σᴸ Σᴿ Γᴸ Γᴿ M M′ A A′}
    {D D′ u u′}
    {Φ : ImpCtx Δᴸ Δᴿ}
    {ρ : NarrowingEnv Φ {Σᴸ} {Σᴿ} {Γᴸ} {Γᴿ}}
    {q : ρ ⊢ᵀ A ⊒ A′}
    {p : ρ ⊢ᵀ D ⊒ D′}
    {u⦂ : ρ ⊢ᴸʷ u ⦂ A ⊑ D}
    {u′⦂ : ρ ⊢ᴿʷ u′ ⦂ A′ ⊑ D′}
  → ρ ⊢ᴺ M ⊒ M′ ∶ q
  → dualʷ (u , u⦂) ⨟ⁿᶠ q
      ≐ᶠ p ⨟ᶠⁿ dualʷ (u′ , u′⦂)
    --------------------------------
  → ρ ⊢ᴺ M ⟨ u ⟩ ⊒ M′ ⟨ u′ ⟩ ∶ p
castʷ⊒castʷ {q = q} {p = p} {u⦂ = u⦂} {u′⦂ = u′⦂}
    M⊒M′ (left-eq , right-eq) =
  ⊒castʷ {p = dualʷ (_ , u⦂) ⨟ⁿᶠ q}
    {q = p} {t⦂ = u′⦂}
    (castʷ⊒ {p = q} {q = dualʷ (_ , u⦂) ⨟ⁿᶠ q}
      {s⦂ = u⦂} M⊒M′ (refl , refl))
    (sym left-eq , sym right-eq)

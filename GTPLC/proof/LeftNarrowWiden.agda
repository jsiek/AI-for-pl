module proof.LeftNarrowWiden where

-- File Charter:
--   * States the GTPLC Left Narrowing and Left Widening formulas.
--   * Tracks store changes produced while a cast on the left reduces.
--   * Requires the resulting value to remain related to the right value.
--   * Shares relocation and right narrowing across the left cast square.

open import Data.List using ([]; _∷_)
open import Data.Product using (_×_; _,_; ∃-syntax; Σ-syntax)

open import Types
open import TyStore
open import Coercions
open import Terms
open import Reduction
open import TypeRelocate
open import NarrowWiden
open import FactoredTypeNarrowing
open import EnvironmentNarrowing
open import ImprecisionTheorems using (dualʷ; _⨟ⁿ_)
open import TermNarrowing
open import proof.LeftEnvironmentChange

------------------------------------------------------------------------
-- Left Narrowing
------------------------------------------------------------------------

LeftNarrowing : Set₁
LeftNarrowing =
  ∀ {Δᴸ Δᴿ Σᴸ Σᴿ V V′ A B C C′ D d}
    {Φ : ImpCtx Δᴸ Δᴿ}
    {ρ : NarrowingEnv Φ {Σᴸ} {Σᴿ} {[]} {[]}}
    {pᴸ : ρ ⊢ᴸⁿ A ⊒ C}
    {qᴸ : ρ ⊢ᴸⁿ D ⊒ C}
    {relocation : Φ ⊢ C ≈ C′}
    {pᴿ : ρ ⊢ᴿⁿ C′ ⊒ B}
    {d⊒ : ρ ⊢ᴸⁿ d ⦂ A ⊒ D}
  → StoreWf Δᴸ Σᴸ
  → StoreWf Δᴿ Σᴿ
  → Value V
  → Value V′
  → ρ ⊢ᴺ V ⊒ V′ ∶ (pᴸ ⨟ᶠ relocation ⨟ᶠ pᴿ)
  → ((d , d⊒) ⨟ⁿ qᴸ) ≐ⁿ pᴸ
  → ∃[ χs ] ∃[ W ]
      (V ⟨ d ⟩ —↠[ χs ] W)
    × Value W
    × StoreWf (χs ▶ᵈ Δᴸ) (χs ▶ˢ Σᴸ)
    × Σ[ ρ′ ∈ NarrowingEnv (χs ▶ᵢ Φ)
        {χs ▶ˢ Σᴸ} {Σᴿ} {[]} {[]} ]
      Σ[ changes ∈ LeftEnvChange ρ χs ρ′ ]
        Σ[ qᴸ′ ∈ ρ′ ⊢ᴸⁿ χs ▶ᵗ D ⊒ χs ▶ᵗ C ]
          Σ[ relocation′ ∈ (χs ▶ᵢ Φ) ⊢ χs ▶ᵗ C ≈ C′ ]
            Σ[ pᴿ′ ∈ ρ′ ⊢ᴿⁿ C′ ⊒ B ]
              ρ′ ⊢ᴺ W ⊒ V′
                ∶ (qᴸ′ ⨟ᶠ relocation′ ⨟ᶠ pᴿ′)

------------------------------------------------------------------------
-- Left Widening
------------------------------------------------------------------------

LeftWidening : Set₁
LeftWidening =
  ∀ {Δᴸ Δᴿ Σᴸ Σᴿ V V′ A B C C′ D u}
    {Φ : ImpCtx Δᴸ Δᴿ}
    {ρ : NarrowingEnv Φ {Σᴸ} {Σᴿ} {[]} {[]}}
    {pᴸ : ρ ⊢ᴸⁿ A ⊒ C}
    {qᴸ : ρ ⊢ᴸⁿ D ⊒ C}
    {relocation : Φ ⊢ C ≈ C′}
    {pᴿ : ρ ⊢ᴿⁿ C′ ⊒ B}
    {u⊑ : ρ ⊢ᴸʷ u ⦂ A ⊑ D}
  → StoreWf Δᴸ Σᴸ
  → StoreWf Δᴿ Σᴿ
  → Value V
  → Value V′
  → ρ ⊢ᴺ V ⊒ V′ ∶ (pᴸ ⨟ᶠ relocation ⨟ᶠ pᴿ)
  → (dualʷ (u , u⊑) ⨟ⁿ pᴸ) ≐ⁿ qᴸ
  → ∃[ χs ] ∃[ W ]
      (V ⟨ u ⟩ —↠[ χs ] W)
    × Value W
    × StoreWf (χs ▶ᵈ Δᴸ) (χs ▶ˢ Σᴸ)
    × Σ[ ρ′ ∈ NarrowingEnv (χs ▶ᵢ Φ)
        {χs ▶ˢ Σᴸ} {Σᴿ} {[]} {[]} ]
      Σ[ changes ∈ LeftEnvChange ρ χs ρ′ ]
        Σ[ qᴸ′ ∈ ρ′ ⊢ᴸⁿ χs ▶ᵗ D ⊒ χs ▶ᵗ C ]
          Σ[ relocation′ ∈ (χs ▶ᵢ Φ) ⊢ χs ▶ᵗ C ≈ C′ ]
            Σ[ pᴿ′ ∈ ρ′ ⊢ᴿⁿ C′ ⊒ B ]
              ρ′ ⊢ᴺ W ⊒ V′
                ∶ (qᴸ′ ⨟ᶠ relocation′ ⨟ᶠ pᴿ′)

module proof.LeftNarrowWiden where

-- File Charter:
--   * States the GTPLC Left Narrowing and Left Widening formulas.
--   * Tracks store changes produced while a cast on the left reduces.
--   * Requires the resulting value to remain related to the right value.
--   * Uses endpoint matching instead of coercion duality or equations.

open import Data.List using ([]; _∷_)
open import Data.Product using (_×_; _,_; ∃-syntax; Σ-syntax)

open import Types
open import TyStore
open import Coercions
open import Terms
open import Reduction
open import TypeNarrow
open import NarrowWiden
open import EnvironmentNarrowing
open import TermNarrowing

------------------------------------------------------------------------
-- Left-side store changes
------------------------------------------------------------------------

leftChangesᵢ : (χs : StoreChanges) → ∀ {Δᴸ Δᴿ}
  → ImpCtx Δᴸ Δᴿ
  → ImpCtx (χs ▶ᵈ Δᴸ) Δᴿ
leftChangesᵢ [] Φ = Φ
leftChangesᵢ (keep ∷ χs) Φ = leftChangesᵢ χs Φ
leftChangesᵢ (bind A ∷ χs) Φ = leftChangesᵢ χs (freshᴸ Φ)

syntax leftChangesᵢ χs Φ = χs ▶ᵢ Φ

------------------------------------------------------------------------
-- Left Narrowing
------------------------------------------------------------------------

LeftNarrowing : Set₁
LeftNarrowing =
  ∀ {Δᴸ Δᴿ Σᴸ Σᴿ V V′ A B D d μ}
    {Φ : ImpCtx Δᴸ Δᴿ}
    {σ : Φ ∣ Δᴸ ⊢ Σᴸ ⊒ˢ Σᴿ ⊣ Δᴿ}
    {r : Φ ⊢ A ⊒ B}
    {p : Φ ⊢ D ⊒ B}
    {d⊒ : μ ∣ Δᴸ ∣ Σᴸ ⊢ d ⦂ A ⊒ D}
  → Value V
  → Value V′
  → (Φ ∣ σ ∣ []ᵍ) ⊢ᴺ V ⊒ V′ ∶ r
  → d⊒ ⨟ p ≈ r
  → ∃[ χs ] ∃[ W ]
      (V ⟨ d ⟩ —↠[ χs ] W)
    × Value W
    × Σ[ σ′ ∈
        χs ▶ᵢ Φ ∣ χs ▶ᵈ Δᴸ
          ⊢ χs ▶ˢ Σᴸ ⊒ˢ Σᴿ ⊣ Δᴿ ]
      Σ[ p′ ∈ χs ▶ᵢ Φ ⊢ χs ▶ᵗ D ⊒ B ]
        ((χs ▶ᵢ Φ ∣ σ′ ∣ []ᵍ) ⊢ᴺ W ⊒ V′ ∶ p′)

------------------------------------------------------------------------
-- Left Widening
------------------------------------------------------------------------

LeftWidening : Set₁
LeftWidening =
  ∀ {Δᴸ Δᴿ Σᴸ Σᴿ V V′ A B D u μ}
    {Φ : ImpCtx Δᴸ Δᴿ}
    {σ : Φ ∣ Δᴸ ⊢ Σᴸ ⊒ˢ Σᴿ ⊣ Δᴿ}
    {p : Φ ⊢ A ⊒ B}
    {r : Φ ⊢ D ⊒ B}
    {u⊑ : μ ∣ Δᴸ ∣ Σᴸ ⊢ u ⦂ A ⊑ D}
  → Value V
  → Value V′
  → (Φ ∣ σ ∣ []ᵍ) ⊢ᴺ V ⊒ V′ ∶ p
  → u⊑ ⨟ p ≈ r
  → ∃[ χs ] ∃[ W ]
      (V ⟨ u ⟩ —↠[ χs ] W)
    × Value W
    × Σ[ σ′ ∈
        χs ▶ᵢ Φ ∣ χs ▶ᵈ Δᴸ
          ⊢ χs ▶ˢ Σᴸ ⊒ˢ Σᴿ ⊣ Δᴿ ]
      Σ[ r′ ∈ χs ▶ᵢ Φ ⊢ χs ▶ᵗ D ⊒ B ]
        ((χs ▶ᵢ Φ ∣ σ′ ∣ []ᵍ) ⊢ᴺ W ⊒ V′ ∶ r′)

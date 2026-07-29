module proof.LeftNarrowWiden where

-- File Charter:
--   * States the GTPLC Left Narrowing and Left Widening formulas.
--   * Tracks store changes produced while a cast on the left reduces.
--   * Requires the resulting value to remain related to the right value.
--   * Does not yet provide proofs of either formula.

open import Data.List using ([]; _∷_)
open import Data.Product using (_×_; _,_; ∃-syntax; Σ-syntax)

open import Types
open import TyStore
open import Coercions
open import Terms
open import Reduction
open import NarrowWiden
open import EnvironmentNarrowing
open import ImprecisionTheorems using
  ( dualʷ
  ; _⨟ˡⁿ_
  ; _≐ⁿ_
  )
open import TermNarrowing

------------------------------------------------------------------------
-- Left-side store changes
------------------------------------------------------------------------

leftChangesᵢ : StoreChanges → ImpCtx → ImpCtx
leftChangesᵢ [] Φ = Φ
leftChangesᵢ (keep ∷ χs) Φ = leftChangesᵢ χs Φ
leftChangesᵢ (bind A ∷ χs) Φ = leftChangesᵢ χs (⇑ᴿᵢ Φ)

syntax leftChangesᵢ χs Φ = χs ▶ᵢ Φ

------------------------------------------------------------------------
-- Left Narrowing
------------------------------------------------------------------------

LeftNarrowing : Set₁
LeftNarrowing =
  ∀ {Φ Δᴸ Δᴿ Σᴸ Σᴿ V V′ A B D d}
    {σ : Φ ∣ Δᴸ ⊢ Σᴸ ⊒ˢ Σᴿ ⊣ Δᴿ}
    {r : Φ ∣ Δᴸ ⊢ A ⊒ B ⊣ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ D ⊒ B ⊣ Δᴿ}
    {d⊒ : idᵢ Δᴸ ∣ Δᴸ ⊢ d ⦂ A ⊒ D ⊣ Δᴸ}
    {μ}
  → Value V
  → Value V′
  → Φ ∣ Δᴸ ∣ Δᴿ ∣ σ ∣ []ᵍ ⊢ᴺ V ⊒ V′ ⦂ A ⊒ B ∶ r
  → μ ∣ Δᴸ ∣ Σᴸ ⊢ d ∶ A =⇒ D
  → (d , d⊒) ⨟ˡⁿ p ≐ⁿ r
  → ∃[ χs ] ∃[ W ]
      (V ⟨ d ⟩ —↠[ χs ] W)
    × Value W
    × Σ[ σ′ ∈ χs ▶ᵢ Φ ∣ χs ▶ᵈ Δᴸ ⊢ χs ▶ˢ Σᴸ ⊒ˢ Σᴿ ⊣ Δᴿ ]
      Σ[ p′ ∈ χs ▶ᵢ Φ ∣ χs ▶ᵈ Δᴸ ⊢ χs ▶ᵗ D ⊒ B ⊣ Δᴿ ]
        (p′ ≐ⁿ p)
      × (χs ▶ᵢ Φ ∣ χs ▶ᵈ Δᴸ ∣ Δᴿ ∣ σ′ ∣ []ᵍ ⊢ᴺ W ⊒ V′ ⦂ χs ▶ᵗ D ⊒ B ∶ p′)

------------------------------------------------------------------------
-- Left Widening
------------------------------------------------------------------------

LeftWidening : Set₁
LeftWidening =
  ∀ {Φ Δᴸ Δᴿ Σᴸ Σᴿ V V′ A B D u}
    {σ : Φ ∣ Δᴸ ⊢ Σᴸ ⊒ˢ Σᴿ ⊣ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊒ B ⊣ Δᴿ}
    {r : Φ ∣ Δᴸ ⊢ D ⊒ B ⊣ Δᴿ}
    {u⊑ : idᵢ Δᴸ ∣ Δᴸ ⊢ u ⦂ A ⊑ D ⊣ Δᴸ}
    {μ}
  → Value V
  → Value V′
  → Φ ∣ Δᴸ ∣ Δᴿ ∣ σ ∣ []ᵍ ⊢ᴺ V ⊒ V′ ⦂ A ⊒ B ∶ p
  → μ ∣ Δᴸ ∣ Σᴸ ⊢ u ∶ A =⇒ D
  → dualʷ (u , u⊑) ⨟ˡⁿ p ≐ⁿ r
  → ∃[ χs ] ∃[ W ]
      (V ⟨ u ⟩ —↠[ χs ] W)
    × Value W
    × Σ[ σ′ ∈ χs ▶ᵢ Φ ∣ χs ▶ᵈ Δᴸ ⊢ χs ▶ˢ Σᴸ ⊒ˢ Σᴿ ⊣ Δᴿ ]
      Σ[ r′ ∈ χs ▶ᵢ Φ ∣ χs ▶ᵈ Δᴸ ⊢ χs ▶ᵗ D ⊒ B ⊣ Δᴿ ]
        (r′ ≐ⁿ r)
      × (χs ▶ᵢ Φ ∣ χs ▶ᵈ Δᴸ ∣ Δᴿ ∣ σ′ ∣ []ᵍ ⊢ᴺ W ⊒ V′ ⦂ χs ▶ᵗ D ⊒ B ∶ r′)

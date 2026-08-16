module proof.DGG.SimBackDef where

-- File Charter:
--   * States closed multi-step backward simulation when the more precise
--     left term reduces.
--   * Allows a residual left trace, matching the GTLC sim-back* proof shape,
--     and records the accumulated parked-world evolution.
--   * Contains no simulation proof.

open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax)

open import Types using (Ty; TyCtx)
open import CastTerms using (Term)
open import Reduction using (StoreChanges; applyTys; _—↠[_]_)
import proof.DGG.CastTermImprecision2 as CTI2
open import proof.DGG.Parked.ParkedWorldDef
  using (ParkedWorld; ParkedEvolve)
open import proof.DGG.Catchup.ValueCatchupRightDef using (_++χ_)
open CTI2 using (World; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_)


SimBack*ᵀ : Set
SimBack*ᵀ =
  ∀ {Δᴸ Δᴿ Δ Δᴸ′} {W : World Δᴸ Δᴿ Δ}
    {M : Term Δᴸ} {M′ : Term Δᴿ} {N : Term Δᴸ′}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ B}
    {χsᴸ : StoreChanges Δᴸ Δᴸ′}
  → ParkedWorld W
  → W ∣ [] ⊢² M ⊑ M′ ∶ p
  → M —↠[ χsᴸ ] N
  → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ N′ ∈ Term Δᴿ′ ] Σ[ Δᴸ″ ∈ TyCtx ]
    Σ[ ψsᴸ ∈ StoreChanges Δᴸ′ Δᴸ″ ] Σ[ N₂ ∈ Term Δᴸ″ ]
    Σ[ Δ′ ∈ TyCtx ] Σ[ W′ ∈ World Δᴸ″ Δᴿ′ Δ′ ]
    Σ[ q ∈ applyTys ψsᴸ (applyTys χsᴸ A)
        ⊑ᵂ⟨ W′ ⟩ applyTys χsᴿ B ]
      (M′ —↠[ χsᴿ ] N′) ×
      (N —↠[ ψsᴸ ] N₂) ×
      ParkedEvolve (χsᴸ ++χ ψsᴸ) χsᴿ W W′ ×
      (W′ ∣ [] ⊢² N₂ ⊑ N′ ∶ q)

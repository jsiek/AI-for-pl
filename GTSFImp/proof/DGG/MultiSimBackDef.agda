module proof.DGG.MultiSimBackDef where

-- File Charter:
--   * States closed multi-step backward simulation when the less precise
--     right term reduces.
--   * Allows a residual right trace and records the accumulated parked-world
--     evolution, unless the more precise left term has already reached blame.
--   * Contains no simulation proof.

open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax; ∃-syntax)
open import Data.Sum using (_⊎_)

open import Types using (Ty; TyCtx)
open import CastTerms using (Term; blame)
open import Reduction using (StoreChanges; applyTys; _—↠[_]_)
import proof.DGG.CastTermImprecision as CTI2
import proof.DGG.CtxImp as CTX
open import proof.DGG.Parked.ParkedWorldDef
  using (ParkedWorld; ParkedEvolve)
open import proof.Reduction using (_++χ_)
open CTX using
  (World;
   _⊑ᵂ⟨_⟩_)
open CTI2 using (_∣_⊢²_⊑_∶_)


SimBack*ᵀ : Set
SimBack*ᵀ =
  ∀ {Δᴸ Δᴿ Δ Δᴿ′} {W : World Δᴸ Δᴿ Δ}
    {M : Term Δᴸ} {M′ : Term Δᴿ} {N′ : Term Δᴿ′}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ B}
    {χsᴿ : StoreChanges Δᴿ Δᴿ′}
  → ParkedWorld W
  → W ∣ [] ⊢² M ⊑ M′ ∶ p
  → M′ —↠[ χsᴿ ] N′
  → (Σ[ Δᴸ′ ∈ TyCtx ] Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
    Σ[ N ∈ Term Δᴸ′ ] Σ[ Δᴿ″ ∈ TyCtx ]
    Σ[ ψsᴿ ∈ StoreChanges Δᴿ′ Δᴿ″ ]
    Σ[ N₂′ ∈ Term Δᴿ″ ]
    Σ[ Δ′ ∈ TyCtx ] Σ[ W′ ∈ World Δᴸ′ Δᴿ″ Δ′ ]
    Σ[ q ∈ applyTys χsᴸ A
        ⊑ᵂ⟨ W′ ⟩ applyTys ψsᴿ (applyTys χsᴿ B) ]
      (M —↠[ χsᴸ ] N) ×
      (N′ —↠[ ψsᴿ ] N₂′) ×
      ParkedEvolve χsᴸ (χsᴿ ++χ ψsᴿ) W W′ ×
      (W′ ∣ [] ⊢² N ⊑ N₂′ ∶ q))
    ⊎ (∃[ Δᴸ′ ] Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
        (M —↠[ χsᴸ ] blame))

module proof.DGG.SimBackDef where

-- File Charter:
--   * States closed one-step backward simulation when the less precise right
--     term reduces.
--   * Allows the more precise left term to take a store-changing trace and
--     records the resulting parked-world evolution.
--   * Contains no simulation proof.

open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax)

open import Types using (Ty; TyCtx)
open import CastTerms using (Term)
open import Reduction using
  ( StoreChange
  ; StoreChanges
  ; applyTy
  ; applyTys
  ; _—→[_]_
  ; _—↠[_]_
  ) renaming ([] to []ˢ; _∷_ to _∷ˢ_)
import proof.DGG.CastTermImprecision as CTI2
import proof.DGG.CtxImp as CTX
open import proof.DGG.Parked.ParkedWorldDef
  using (ParkedWorld; ParkedEvolve)
open CTX using
  (World;
   _⊑ᵂ⟨_⟩_)
open CTI2 using (_∣_⊢²_⊑_∶_)


SimBackᵀ : Set
SimBackᵀ =
  ∀ {Δᴸ Δᴿ Δ Δᴿ′} {W : World Δᴸ Δᴿ Δ}
    {M : Term Δᴸ} {M′ : Term Δᴿ} {N′ : Term Δᴿ′}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ B}
    {χᴿ : StoreChange Δᴿ Δᴿ′}
  → ParkedWorld W
  → W ∣ [] ⊢² M ⊑ M′ ∶ p
  → M′ —→[ χᴿ ] N′
  → Σ[ Δᴸ′ ∈ TyCtx ] Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
    Σ[ N ∈ Term Δᴸ′ ] Σ[ Δ′ ∈ TyCtx ]
    Σ[ W′ ∈ World Δᴸ′ Δᴿ′ Δ′ ]
    Σ[ q ∈ applyTys χsᴸ A ⊑ᵂ⟨ W′ ⟩ applyTy χᴿ B ]
      (M —↠[ χsᴸ ] N) ×
      ParkedEvolve χsᴸ (χᴿ ∷ˢ []ˢ) W W′ ×
      (W′ ∣ [] ⊢² N ⊑ N′ ∶ q)

module proof.DGG.SimDef where

-- File Charter:
--   * States closed one-step simulation when the more precise left term
--     reduces.
--   * Allows the less precise right term to take a store-changing trace and
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
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.CtxImp as CTX
open import proof.DGG.Parked.ParkedWorldDef
  using (ParkedWorld; ParkedEvolve)
open CTX using
  (World;
   _⊑ᵂ⟨_⟩_)
open CTI2 using (_∣_⊢²_⊑_∶_)


Simᵀ : Set
Simᵀ =
  ∀ {Δᴸ Δᴿ Δ Δᴸ′} {W : World Δᴸ Δᴿ Δ}
    {M : Term Δᴸ} {M′ : Term Δᴿ} {N : Term Δᴸ′}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ B}
    {χᴸ : StoreChange Δᴸ Δᴸ′}
  → ParkedWorld W
  → W ∣ [] ⊢² M ⊑ M′ ∶ p
  → M —→[ χᴸ ] N
  → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ N′ ∈ Term Δᴿ′ ] Σ[ Δ′ ∈ TyCtx ]
    Σ[ W′ ∈ World Δᴸ′ Δᴿ′ Δ′ ]
    Σ[ q ∈ applyTy χᴸ A ⊑ᵂ⟨ W′ ⟩ applyTys χsᴿ B ]
      (M′ —↠[ χsᴿ ] N′) ×
      ParkedEvolve (χᴸ ∷ˢ []ˢ) χsᴿ W W′ ×
      (W′ ∣ [] ⊢² N ⊑ N′ ∶ q)

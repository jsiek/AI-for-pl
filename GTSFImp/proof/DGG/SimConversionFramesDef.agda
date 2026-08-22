module proof.DGG.SimConversionFramesDef where

-- File Charter:
--   * States structural simulation beneath reveal and conceal boundaries.
--   * Separates non-value frame replay from terminal value closing.
--   * Contains no reveal/conceal frame simulation proofs.

open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax)

open import Types using (Ty; TyCtx)
open import Conversion using (Conv↑; Conv↓)
open import CastTerms using (Term; _↑_; _↓_)
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


record SimConversionFramesᵀ : Set₁ where
  field
    source-reveal-frame :
      ∀ {Δᴸ Δᴿ Δ Δᴸ′} {W : World Δᴸ Δᴿ Δ}
        {M : Term Δᴸ} {M′ : Term Δᴿ} {N : Term Δᴸ′}
        {A A′ : Ty Δᴸ} {B : Ty Δᴿ}
        {c : Conv↑ Δᴸ A A′} {q : A′ ⊑ᵂ⟨ W ⟩ B}
        {χᴸ : StoreChange Δᴸ Δᴸ′}
      → ParkedWorld W
      → W ∣ [] ⊢² M ↑ c ⊑ M′ ∶ q
      → M ↑ c —→[ χᴸ ] N
      → Σ[ Δᴿ′ ∈ TyCtx ]
        Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
        Σ[ N′ ∈ Term Δᴿ′ ] Σ[ Δ′ ∈ TyCtx ]
        Σ[ W′ ∈ World Δᴸ′ Δᴿ′ Δ′ ]
        Σ[ r ∈ applyTy χᴸ A′ ⊑ᵂ⟨ W′ ⟩
            applyTys χsᴿ B ]
          (M′ —↠[ χsᴿ ] N′) ×
          ParkedEvolve (χᴸ ∷ˢ []ˢ) χsᴿ W W′ ×
          (W′ ∣ [] ⊢² N ⊑ N′ ∶ r)

    target-reveal-frame :
      ∀ {Δᴸ Δᴿ Δ Δᴸ′} {W : World Δᴸ Δᴿ Δ}
        {M : Term Δᴸ} {M′ : Term Δᴿ} {N : Term Δᴸ′}
        {A : Ty Δᴸ} {B B′ : Ty Δᴿ}
        {c′ : Conv↑ Δᴿ B B′} {q : A ⊑ᵂ⟨ W ⟩ B′}
        {χᴸ : StoreChange Δᴸ Δᴸ′}
      → ParkedWorld W
      → W ∣ [] ⊢² M ⊑ M′ ↑ c′ ∶ q
      → M —→[ χᴸ ] N
      → Σ[ Δᴿ′ ∈ TyCtx ]
        Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
        Σ[ N′ ∈ Term Δᴿ′ ] Σ[ Δ′ ∈ TyCtx ]
        Σ[ W′ ∈ World Δᴸ′ Δᴿ′ Δ′ ]
        Σ[ r ∈ applyTy χᴸ A ⊑ᵂ⟨ W′ ⟩
            applyTys χsᴿ B′ ]
          (M′ ↑ c′ —↠[ χsᴿ ] N′) ×
          ParkedEvolve (χᴸ ∷ˢ []ˢ) χsᴿ W W′ ×
          (W′ ∣ [] ⊢² N ⊑ N′ ∶ r)

    source-conceal-frame :
      ∀ {Δᴸ Δᴿ Δ Δᴸ′} {W : World Δᴸ Δᴿ Δ}
        {M : Term Δᴸ} {M′ : Term Δᴿ} {N : Term Δᴸ′}
        {A A′ : Ty Δᴸ} {B : Ty Δᴿ}
        {c : Conv↓ Δᴸ A A′} {q : A′ ⊑ᵂ⟨ W ⟩ B}
        {χᴸ : StoreChange Δᴸ Δᴸ′}
      → ParkedWorld W
      → W ∣ [] ⊢² M ↓ c ⊑ M′ ∶ q
      → M ↓ c —→[ χᴸ ] N
      → Σ[ Δᴿ′ ∈ TyCtx ]
        Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
        Σ[ N′ ∈ Term Δᴿ′ ] Σ[ Δ′ ∈ TyCtx ]
        Σ[ W′ ∈ World Δᴸ′ Δᴿ′ Δ′ ]
        Σ[ r ∈ applyTy χᴸ A′ ⊑ᵂ⟨ W′ ⟩
            applyTys χsᴿ B ]
          (M′ —↠[ χsᴿ ] N′) ×
          ParkedEvolve (χᴸ ∷ˢ []ˢ) χsᴿ W W′ ×
          (W′ ∣ [] ⊢² N ⊑ N′ ∶ r)

    target-conceal-frame :
      ∀ {Δᴸ Δᴿ Δ Δᴸ′} {W : World Δᴸ Δᴿ Δ}
        {M : Term Δᴸ} {M′ : Term Δᴿ} {N : Term Δᴸ′}
        {A : Ty Δᴸ} {B B′ : Ty Δᴿ}
        {c′ : Conv↓ Δᴿ B B′} {q : A ⊑ᵂ⟨ W ⟩ B′}
        {χᴸ : StoreChange Δᴸ Δᴸ′}
      → ParkedWorld W
      → W ∣ [] ⊢² M ⊑ M′ ↓ c′ ∶ q
      → M —→[ χᴸ ] N
      → Σ[ Δᴿ′ ∈ TyCtx ]
        Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
        Σ[ N′ ∈ Term Δᴿ′ ] Σ[ Δ′ ∈ TyCtx ]
        Σ[ W′ ∈ World Δᴸ′ Δᴿ′ Δ′ ]
        Σ[ r ∈ applyTy χᴸ A ⊑ᵂ⟨ W′ ⟩
            applyTys χsᴿ B′ ]
          (M′ ↓ c′ —↠[ χsᴿ ] N′) ×
          ParkedEvolve (χᴸ ∷ˢ []ˢ) χsᴿ W W′ ×
          (W′ ∣ [] ⊢² N ⊑ N′ ∶ r)

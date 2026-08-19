module proof.DGG.SimCastLayerInversion where

-- File Charter:
--   * Provides one-layer source ordinary-cast head-analysis views for CTX.
--   * Exposes the layer's inner imprecision witness without performing
--     recursive analysis of the premise.
--   * Separates the two D2a heads, `cast⊑²` and `cast⊑cast²`, from
--     target-wrapper heads, which remain blocked in the view.

open import Types using (Ty)
open import Conversion using (Conv↑; Conv↓)
open import Consistency using (Env∼; _⊢_∼_)
open import CastTerms using (Term; _⟨_⟩; _↑_; _↓_)
import Conversion as Conv
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.CtxImp as CTX
open CTX using
  (World;
   CtxImp;
   ImpEnvMono;
   RebaseAtᴿ;
   SameCtx;
   targetStoreʷ;
   _⊑ᵂ⟨_⟩_)
open CTI2 using (_∣_⊢²_⊑_∶_)


data SourceCastLayerHeadView {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) (γ : CtxImp W)
    {A B : Ty Δᴸ} {ν : Env∼ Δᴸ}
    (M : Term Δᴸ) (c : ν ⊢ A ∼ B) :
    {C : Ty Δᴿ} → Term Δᴿ → B ⊑ᵂ⟨ W ⟩ C → Set where

  source-cast-layer : ∀ {C M′} {q : B ⊑ᵂ⟨ W ⟩ C}
    → (p : A ⊑ᵂ⟨ W ⟩ C)
    → W ∣ γ ⊢² M ⊑ M′ ∶ p
      ------------------------------------------------
    → SourceCastLayerHeadView W γ M c M′ q

  paired-source-cast-layer :
      ∀ {C C′ M′} {ν′ : Env∼ Δᴿ}
        {c′ : ν′ ⊢ C′ ∼ C} {q : B ⊑ᵂ⟨ W ⟩ C}
    → (p : A ⊑ᵂ⟨ W ⟩ C′)
    → W ∣ γ ⊢² M ⊑ M′ ∶ p
      -----------------------------------------------------
    → SourceCastLayerHeadView W γ M c (M′ ⟨ c′ ⟩) q

  target-cast-layer-blocked :
      ∀ {C C′ M′} {ν′ : Env∼ Δᴿ}
        {c′ : ν′ ⊢ C′ ∼ C} {q : B ⊑ᵂ⟨ W ⟩ C}
    → (p : B ⊑ᵂ⟨ W ⟩ C′)
    → W ∣ γ ⊢² M ⟨ c ⟩ ⊑ M′ ∶ p
      -----------------------------------------------------
    → SourceCastLayerHeadView W γ M c (M′ ⟨ c′ ⟩) q

  target-reveal-layer-blocked :
      ∀ {C C′ M′ W′ γ′ Xᴿ?}
        {c′ : Conv↑ Δᴿ C′ C} {q : B ⊑ᵂ⟨ W ⟩ C}
    → ImpEnvMono W W′
    → RebaseAtᴿ W W′ Xᴿ?
    → SameCtx γ γ′
    → targetStoreʷ W Conv.⊢↑[ Xᴿ? ] c′
    → (p : B ⊑ᵂ⟨ W′ ⟩ C′)
    → W′ ∣ γ′ ⊢² M ⟨ c ⟩ ⊑ M′ ∶ p
      ------------------------------------------------
    → SourceCastLayerHeadView W γ M c (M′ ↑ c′) q

  target-conceal-layer-blocked :
      ∀ {C C′ M′ W′ γ′ Xᴿ?}
        {c′ : Conv↓ Δᴿ C′ C} {q : B ⊑ᵂ⟨ W ⟩ C}
    → ImpEnvMono W W′
    → RebaseAtᴿ W′ W Xᴿ?
    → SameCtx γ γ′
    → targetStoreʷ W Conv.⊢↓[ Xᴿ? ] c′
    → (p : B ⊑ᵂ⟨ W′ ⟩ C′)
    → W′ ∣ γ′ ⊢² M ⟨ c ⟩ ⊑ M′ ∶ p
      ------------------------------------------------
    → SourceCastLayerHeadView W γ M c (M′ ↓ c′) q


source-cast-layer-head-analysis : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A B : Ty Δᴸ} {C : Ty Δᴿ}
    {ν : Env∼ Δᴸ} {c : ν ⊢ A ∼ B}
    {q : B ⊑ᵂ⟨ W ⟩ C}
  → W ∣ γ ⊢² M ⟨ c ⟩ ⊑ M′ ∶ q
    ------------------------------------
  → SourceCastLayerHeadView W γ M c M′ q
source-cast-layer-head-analysis (CTI2.cast⊑cast² c c′ rel q) =
  paired-source-cast-layer _ rel
source-cast-layer-head-analysis (CTI2.⊑cast² c′ rel q) =
  target-cast-layer-blocked _ rel
source-cast-layer-head-analysis (CTI2.⊑reveal² mono rb sc c′⊢ rel q) =
  target-reveal-layer-blocked mono rb sc c′⊢ _ rel
source-cast-layer-head-analysis (CTI2.⊑conceal² mono rb sc c′⊢ rel q) =
  target-conceal-layer-blocked mono rb sc c′⊢ _ rel
source-cast-layer-head-analysis (CTI2.cast⊑² c rel q) =
  source-cast-layer _ rel

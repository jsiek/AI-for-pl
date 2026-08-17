module proof.DGG.SimCastLayerInversion where

-- File Charter:
--   * Provides one-layer source ordinary-cast head-analysis views for CTI2.
--   * Exposes the layer's inner imprecision witness without performing
--     recursive analysis of the premise.
--   * Separates the two D2a heads, `cast⊑²` and `cast⊑cast²`, from
--     target-wrapper heads that require a later peel/replay ruling.

open import Types using (Ty)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ-syntax; _,_)
open import Conversion using (Conv↑; Conv↓)
open import Consistency using (Env∼; _⊢_∼_)
open import CastTerms using (Term; Value; _⟨_⟩; _↑_; _↓_)
import CastTerms as CT
import proof.DGG.CastTermImprecision2 as CTI2
open CTI2 using
  ( World
  ; CtxImp
  ; ImpEnvMono
  ; RebaseAtᴿ
  ; SameCtx
  ; targetStoreʷ
  ; _⊢↑[_]_
  ; _⊢↓[_]_
  ; _⊑ᵂ⟨_⟩_
  ; _∣_⊢²_⊑_∶_
  )


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
    → targetStoreʷ W ⊢↑[ Xᴿ? ] c′
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
    → targetStoreʷ W ⊢↓[ Xᴿ? ] c′
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


SourceValueCastLayerPeelᵀ : Set
SourceValueCastLayerPeelᵀ =
  ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {V : Term Δᴸ} {V′ : Term Δᴿ}
    {A B : Ty Δᴸ} {C : Ty Δᴿ}
    {ν : Env∼ Δᴸ} {c : ν ⊢ A ∼ B}
    {q : B ⊑ᵂ⟨ W ⟩ C}
  → Value V′
  → W ∣ γ ⊢² V ⟨ c ⟩ ⊑ V′ ∶ q
  → Σ[ p ∈ A ⊑ᵂ⟨ W ⟩ C ] W ∣ γ ⊢² V ⊑ V′ ∶ p

targetValueHeight : ∀ {Δ} {V : Term Δ} → Value V → ℕ
targetValueHeight (CT.ƛ N) = zero
targetValueHeight (CT.Λ vV) = targetValueHeight vV
targetValueHeight (CT.$ k) = zero
targetValueHeight (vV CT.《 inert 》) = suc (targetValueHeight vV)
targetValueHeight (vV CT.↑ rv) = suc (targetValueHeight vV)
targetValueHeight (vV CT.↓ cv) = suc (targetValueHeight vV)

TargetValueCastReplayᵀ : Set
TargetValueCastReplayᵀ =
  ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {V : Term Δᴸ} {V′ : Term Δᴿ}
    {A : Ty Δᴸ} {C D : Ty Δᴿ}
    {ν′ : Env∼ Δᴿ} {c′ : ν′ ⊢ D ∼ C}
    {p : A ⊑ᵂ⟨ W ⟩ D}
  → Value (V′ ⟨ c′ ⟩)
  → W ∣ γ ⊢² V ⊑ V′ ∶ p
  → Σ[ r ∈ A ⊑ᵂ⟨ W ⟩ C ] W ∣ γ ⊢² V ⊑ V′ ⟨ c′ ⟩ ∶ r

TargetValueRevealReplayᵀ : Set
TargetValueRevealReplayᵀ =
  ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ} {γ : CtxImp W} {γ′ : CtxImp W′}
    {V : Term Δᴸ} {V′ : Term Δᴿ}
    {A : Ty Δᴸ} {C D : Ty Δᴿ} {Xᴿ?}
    {c′ : Conv↑ Δᴿ D C}
    {p : A ⊑ᵂ⟨ W′ ⟩ D}
  → Value (V′ ↑ c′)
  → ImpEnvMono W W′
  → RebaseAtᴿ W W′ Xᴿ?
  → SameCtx γ γ′
  → targetStoreʷ W ⊢↑[ Xᴿ? ] c′
  → W′ ∣ γ′ ⊢² V ⊑ V′ ∶ p
  → Σ[ r ∈ A ⊑ᵂ⟨ W ⟩ C ] W ∣ γ ⊢² V ⊑ V′ ↑ c′ ∶ r

TargetValueConcealReplayᵀ : Set
TargetValueConcealReplayᵀ =
  ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ} {γ : CtxImp W} {γ′ : CtxImp W′}
    {V : Term Δᴸ} {V′ : Term Δᴿ}
    {A : Ty Δᴸ} {C D : Ty Δᴿ} {Xᴿ?}
    {c′ : Conv↓ Δᴿ D C}
    {p : A ⊑ᵂ⟨ W′ ⟩ D}
  → Value (V′ ↓ c′)
  → ImpEnvMono W W′
  → RebaseAtᴿ W′ W Xᴿ?
  → SameCtx γ γ′
  → targetStoreʷ W ⊢↓[ Xᴿ? ] c′
  → W′ ∣ γ′ ⊢² V ⊑ V′ ∶ p
  → Σ[ r ∈ A ⊑ᵂ⟨ W ⟩ C ] W ∣ γ ⊢² V ⊑ V′ ↓ c′ ∶ r

record SourceValueCastLayerPeelResiduals : Set₁ where
  field
    target-value-cast-replay : TargetValueCastReplayᵀ
    target-value-reveal-replay : TargetValueRevealReplayᵀ
    target-value-conceal-replay : TargetValueConcealReplayᵀ

source-value-cast-layer-peel-with :
  SourceValueCastLayerPeelResiduals → SourceValueCastLayerPeelᵀ
source-value-cast-layer-peel-with residuals vV′
    (CTI2.cast⊑² c rel q) =
  _ , rel
source-value-cast-layer-peel-with residuals (vV′ CT.《 inert 》)
    (CTI2.cast⊑cast² c c′ rel q) =
  SourceValueCastLayerPeelResiduals.target-value-cast-replay residuals
    (vV′ CT.《 inert 》) rel
source-value-cast-layer-peel-with residuals (vV′ CT.《 inert 》)
    (CTI2.⊑cast² c′ rel q)
    with source-value-cast-layer-peel-with residuals vV′ rel
source-value-cast-layer-peel-with residuals (vV′ CT.《 inert 》)
    (CTI2.⊑cast² c′ rel q) | p , rel′ =
  SourceValueCastLayerPeelResiduals.target-value-cast-replay residuals
    (vV′ CT.《 inert 》) rel′
source-value-cast-layer-peel-with residuals (vV′ CT.↑ rv)
    (CTI2.⊑reveal² mono rb sc c′⊢ rel q)
    with source-value-cast-layer-peel-with residuals vV′ rel
source-value-cast-layer-peel-with residuals (vV′ CT.↑ rv)
    (CTI2.⊑reveal² mono rb sc c′⊢ rel q) | p , rel′ =
  SourceValueCastLayerPeelResiduals.target-value-reveal-replay residuals
    (vV′ CT.↑ rv) mono rb sc c′⊢ rel′
source-value-cast-layer-peel-with residuals (vV′ CT.↓ cv)
    (CTI2.⊑conceal² mono rb sc c′⊢ rel q)
    with source-value-cast-layer-peel-with residuals vV′ rel
source-value-cast-layer-peel-with residuals (vV′ CT.↓ cv)
    (CTI2.⊑conceal² mono rb sc c′⊢ rel q) | p , rel′ =
  SourceValueCastLayerPeelResiduals.target-value-conceal-replay residuals
    (vV′ CT.↓ cv) mono rb sc c′⊢ rel′

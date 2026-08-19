module proof.DGG.SimPairedCastValuesProof where

-- File Charter:
--   * Implements the direct paired ordinary-cast value rows.
--   * Rewraps the target cast in the β-id row with `⊑cast²`.
--   * Names the remaining source-side cast rebuild obligations as residuals,
--     keeping β-inst residual.

open import Data.Empty using (⊥-elim)
open import Data.List using ([])
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.Unit.Base using (⊤; tt)

open import Types using (Ty; TyCtx)
open import Consistency using (Env∼; _⊢_∼_)
open import CastTerms using (Term; Value; _⟨_⟩)
open import Reduction using
  ( StoreChange
  ; StoreChanges
  ; applyTy
  ; applyTys
  ; _—→[_]_
  ; _—↠[_]_
  ; pure-step
  ; β-id
  ; ground
  ; expand
  ; tag-untag
  ; tag-untag-bad
  ; blame-bot-intro
  ; blame-⟨⟩
  ; β-inst
  ; ξ-⟨⟩
  ) renaming ([] to []ˢ; _∷_ to _∷ˢ_)
import Reduction as R
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.CtxImp as CTX
import proof.DGG.CastTermImprecision2Typing as CTI2T
open import proof.DGG.Parked.ParkedWorldDef
  using (ParkedWorld; ParkedEvolve; evolve-refl; evolve-keepᴸ)
open CTX using
  (World;
   _⊑ᵂ⟨_⟩_)
open CTI2 using (_∣_⊢²_⊑_∶_)
open import proof.DGG.SimPairedCastValuesDef
  using (SimPairedCastValuesᵀ)
open import proof.Reduction.ValueIrreducibleProof
  using (value-no-step)


PairedCastRel : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ B}
  → W ∣ [] ⊢² M ⊑ M′ ∶ p → Set
PairedCastRel (CTI2.cast⊑cast² _ _ _ _) = ⊤
PairedCastRel _ = Data.Empty.⊥

GroundStep : ∀ {Δ Δ′ : TyCtx}
    {M : Term Δ} {χ : StoreChange Δ Δ′} {N : Term Δ′}
  → M —→[ χ ] N → Set
GroundStep (pure-step (ground _ _)) = ⊤
GroundStep _ = Data.Empty.⊥

ExpandStep : ∀ {Δ Δ′ : TyCtx}
    {M : Term Δ} {χ : StoreChange Δ Δ′} {N : Term Δ′}
  → M —→[ χ ] N → Set
ExpandStep (pure-step (expand _ _)) = ⊤
ExpandStep _ = Data.Empty.⊥

TagUntagStep : ∀ {Δ Δ′ : TyCtx}
    {M : Term Δ} {χ : StoreChange Δ Δ′} {N : Term Δ′}
  → M —→[ χ ] N → Set
TagUntagStep (pure-step (tag-untag _)) = ⊤
TagUntagStep _ = Data.Empty.⊥

βInstStep : ∀ {Δ Δ′ : TyCtx}
    {M : Term Δ} {χ : StoreChange Δ Δ′} {N : Term Δ′}
  → M —→[ χ ] N → Set
βInstStep (β-inst _ _) = ⊤
βInstStep _ = Data.Empty.⊥


record SimPairedCastValuesResiduals : Set where
  field
    paired-ground-row : ∀ {Δᴸ Δᴿ Δ Δᴸ′}
        {W : World Δᴸ Δᴿ Δ} {χᴸ : StoreChange Δᴸ Δᴸ′}
        {V : Term Δᴸ} {V′ : Term Δᴿ} {N : Term Δᴸ′}
        {A B : Ty Δᴸ} {A′ B′ : Ty Δᴿ}
        {μ : Env∼ Δᴸ} {μ′ : Env∼ Δᴿ}
        {c : μ ⊢ A ∼ B} {c′ : μ′ ⊢ A′ ∼ B′}
        {q : B ⊑ᵂ⟨ W ⟩ B′}
      → ParkedWorld W
      → (rel : W ∣ [] ⊢² V ⟨ c ⟩ ⊑ V′ ⟨ c′ ⟩ ∶ q)
      → PairedCastRel rel
      → Value V
      → Value V′
      → (step : V ⟨ c ⟩ —→[ χᴸ ] N)
      → GroundStep step
      → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
        Σ[ N′ ∈ Term Δᴿ′ ] Σ[ Δ′ ∈ TyCtx ]
        Σ[ W′ ∈ World Δᴸ′ Δᴿ′ Δ′ ]
        Σ[ r ∈ applyTy χᴸ B ⊑ᵂ⟨ W′ ⟩ applyTys χsᴿ B′ ]
          (V′ ⟨ c′ ⟩ —↠[ χsᴿ ] N′) ×
          ParkedEvolve (χᴸ ∷ˢ []ˢ) χsᴿ W W′ ×
          (W′ ∣ [] ⊢² N ⊑ N′ ∶ r)

    paired-expand-row : ∀ {Δᴸ Δᴿ Δ Δᴸ′}
        {W : World Δᴸ Δᴿ Δ} {χᴸ : StoreChange Δᴸ Δᴸ′}
        {V : Term Δᴸ} {V′ : Term Δᴿ} {N : Term Δᴸ′}
        {A B : Ty Δᴸ} {A′ B′ : Ty Δᴿ}
        {μ : Env∼ Δᴸ} {μ′ : Env∼ Δᴿ}
        {c : μ ⊢ A ∼ B} {c′ : μ′ ⊢ A′ ∼ B′}
        {q : B ⊑ᵂ⟨ W ⟩ B′}
      → ParkedWorld W
      → (rel : W ∣ [] ⊢² V ⟨ c ⟩ ⊑ V′ ⟨ c′ ⟩ ∶ q)
      → PairedCastRel rel
      → Value V
      → Value V′
      → (step : V ⟨ c ⟩ —→[ χᴸ ] N)
      → ExpandStep step
      → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
        Σ[ N′ ∈ Term Δᴿ′ ] Σ[ Δ′ ∈ TyCtx ]
        Σ[ W′ ∈ World Δᴸ′ Δᴿ′ Δ′ ]
        Σ[ r ∈ applyTy χᴸ B ⊑ᵂ⟨ W′ ⟩ applyTys χsᴿ B′ ]
          (V′ ⟨ c′ ⟩ —↠[ χsᴿ ] N′) ×
          ParkedEvolve (χᴸ ∷ˢ []ˢ) χsᴿ W W′ ×
          (W′ ∣ [] ⊢² N ⊑ N′ ∶ r)

    paired-tag-untag-row : ∀ {Δᴸ Δᴿ Δ Δᴸ′}
        {W : World Δᴸ Δᴿ Δ} {χᴸ : StoreChange Δᴸ Δᴸ′}
        {V : Term Δᴸ} {V′ : Term Δᴿ} {N : Term Δᴸ′}
        {A B : Ty Δᴸ} {A′ B′ : Ty Δᴿ}
        {μ : Env∼ Δᴸ} {μ′ : Env∼ Δᴿ}
        {c : μ ⊢ A ∼ B} {c′ : μ′ ⊢ A′ ∼ B′}
        {q : B ⊑ᵂ⟨ W ⟩ B′}
      → ParkedWorld W
      → (rel : W ∣ [] ⊢² V ⟨ c ⟩ ⊑ V′ ⟨ c′ ⟩ ∶ q)
      → PairedCastRel rel
      → Value V
      → Value V′
      → (step : V ⟨ c ⟩ —→[ χᴸ ] N)
      → TagUntagStep step
      → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
        Σ[ N′ ∈ Term Δᴿ′ ] Σ[ Δ′ ∈ TyCtx ]
        Σ[ W′ ∈ World Δᴸ′ Δᴿ′ Δ′ ]
        Σ[ r ∈ applyTy χᴸ B ⊑ᵂ⟨ W′ ⟩ applyTys χsᴿ B′ ]
          (V′ ⟨ c′ ⟩ —↠[ χsᴿ ] N′) ×
          ParkedEvolve (χᴸ ∷ˢ []ˢ) χsᴿ W W′ ×
          (W′ ∣ [] ⊢² N ⊑ N′ ∶ r)

    paired-β-inst-row : ∀ {Δᴸ Δᴿ Δ Δᴸ′}
        {W : World Δᴸ Δᴿ Δ} {χᴸ : StoreChange Δᴸ Δᴸ′}
        {V : Term Δᴸ} {V′ : Term Δᴿ} {N : Term Δᴸ′}
        {A B : Ty Δᴸ} {A′ B′ : Ty Δᴿ}
        {μ : Env∼ Δᴸ} {μ′ : Env∼ Δᴿ}
        {c : μ ⊢ A ∼ B} {c′ : μ′ ⊢ A′ ∼ B′}
        {q : B ⊑ᵂ⟨ W ⟩ B′}
      → ParkedWorld W
      → (rel : W ∣ [] ⊢² V ⟨ c ⟩ ⊑ V′ ⟨ c′ ⟩ ∶ q)
      → PairedCastRel rel
      → Value V
      → Value V′
      → (step : V ⟨ c ⟩ —→[ χᴸ ] N)
      → βInstStep step
      → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
        Σ[ N′ ∈ Term Δᴿ′ ] Σ[ Δ′ ∈ TyCtx ]
        Σ[ W′ ∈ World Δᴸ′ Δᴿ′ Δ′ ]
        Σ[ r ∈ applyTy χᴸ B ⊑ᵂ⟨ W′ ⟩ applyTys χsᴿ B′ ]
          (V′ ⟨ c′ ⟩ —↠[ χsᴿ ] N′) ×
          ParkedEvolve (χᴸ ∷ˢ []ˢ) χsᴿ W W′ ×
          (W′ ∣ [] ⊢² N ⊑ N′ ∶ r)


sim-paired-cast-values-with :
  SimPairedCastValuesResiduals → SimPairedCastValuesᵀ
sim-paired-cast-values-with residuals {world = W} {V′ = V′}
    {c′ = c′} parked rel q vV vV′ (pure-step (β-id _)) =
  _ , R.[] , V′ ⟨ c′ ⟩ , _ , W , q ,
  R.↠-refl , evolve-keepᴸ evolve-refl , CTI2.⊑cast² c′ rel q
sim-paired-cast-values-with residuals {c = c} {c′ = c′}
    parked rel q vV vV′
    step@(pure-step (ground _ _)) =
  SimPairedCastValuesResiduals.paired-ground-row residuals
    parked (CTI2.cast⊑cast² c c′ rel q) tt vV vV′ step tt
sim-paired-cast-values-with residuals {c = c} {c′ = c′}
    parked rel q vV vV′
    step@(pure-step (expand _ _)) =
  SimPairedCastValuesResiduals.paired-expand-row residuals
    parked (CTI2.cast⊑cast² c c′ rel q) tt vV vV′ step tt
sim-paired-cast-values-with residuals {c = c} {c′ = c′}
    parked rel q vV vV′
    step@(pure-step (tag-untag _)) =
  SimPairedCastValuesResiduals.paired-tag-untag-row residuals
    parked (CTI2.cast⊑cast² c c′ rel q) tt vV vV′ step tt
sim-paired-cast-values-with residuals {world = W} {V′ = V′}
    {c = c} {c′ = c′} parked rel q vV vV′
    (pure-step (tag-untag-bad _ _)) =
  _ , R.[] , V′ ⟨ c′ ⟩ , _ , W , q ,
  R.↠-refl , evolve-keepᴸ evolve-refl ,
  CTI2.blame⊑²
    (CTI2T.target-typing² (CTI2.cast⊑cast² c c′ rel q)) q
sim-paired-cast-values-with residuals {world = W} {V′ = V′}
    {c = c} {c′ = c′} parked rel q vV vV′
    (pure-step (blame-bot-intro _)) =
  _ , R.[] , V′ ⟨ c′ ⟩ , _ , W , q ,
  R.↠-refl , evolve-keepᴸ evolve-refl ,
  CTI2.blame⊑²
    (CTI2T.target-typing² (CTI2.cast⊑cast² c c′ rel q)) q
sim-paired-cast-values-with residuals parked rel q () vV′
    (pure-step blame-⟨⟩)
sim-paired-cast-values-with residuals {c = c} {c′ = c′}
    parked rel q vV vV′
    step@(β-inst _ _) =
  SimPairedCastValuesResiduals.paired-β-inst-row residuals
    parked (CTI2.cast⊑cast² c c′ rel q) tt vV vV′ step tt
sim-paired-cast-values-with residuals parked rel q vV vV′
    (ξ-⟨⟩ step _) =
  ⊥-elim (value-no-step vV step)

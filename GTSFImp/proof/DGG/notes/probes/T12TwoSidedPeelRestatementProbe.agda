module T12TwoSidedPeelRestatementProbe where

-- File Charter:
--   * Statement-only scratch probe for the T12 two-sided peel restatements.
--   * Checks that the proposed replacement surfaces are well-formed Agda
--     `Set` declarations.
--   * Provides no implementations, inhabitants, postulates, holes, or imports
--     from this scratch module into the live DGG development.

open import Data.List using ([])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; Σ-syntax)

open import Types using (Ty; TyCtx; TyVar)
open import Conversion using (Conv↑; Conv↓; seal; unseal)
open import CastTerms using (Term; Value; _↑_; _↓_)
open import Reduction using
  ( StoreChange
  ; StoreChanges
  ; applyTy
  ; applyTys
  ; keep
  ; _—→[_]_
  ; _—↠[_]_
  ) renaming ([] to []ˢ; _∷_ to _∷ˢ_)
import proof.DGG.CastTermImprecision2 as CTI2
open import proof.DGG.Parked.ParkedWorldDef
  using (ParkedWorld; ParkedEvolve)
open import proof.DGG.CatchupToMorePreciseDef
  using
    ( CatchupBoundary
    ; CatchupBoundaryKind
    ; source-reveal-boundary
    ; source-conceal-boundary
    ; target-reveal-boundary
    ; target-conceal-boundary
    )
open CTI2 using
  ( World
  ; CtxImp
  ; ImpEnvMono
  ; RebaseAtᴸ
  ; RebaseAtᴿ
  ; TagRebaseAtᴸ
  ; SameCtx
  ; _⊑ᵂ⟨_⟩_
  ; _∣_⊢²_⊑_∶_
  )


record TargetOpenedByConcealReveal {Δᴿ : TyCtx}
    (V′ : Term Δᴿ) (R′ : Ty Δᴿ) : Set where
  field
    opened-payload : Term Δᴿ
    opened-pivot : TyVar Δᴿ
    opened-value : Value opened-payload
    opened-step :
      ((opened-payload ↓ seal opened-pivot R′)
        ↑ unseal opened-pivot R′) —→[ keep ] V′


PairedConcealRevealPeelᵀ : Set
PairedConcealRevealPeelᵀ =
  ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {V₀ : Term Δᴸ} {V₀′ : Term Δᴿ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
    {R : Ty Δᴸ} {R′ : Ty Δᴿ}
    {q : R ⊑ᵂ⟨ W ⟩ R′}
  → Value V₀
  → Value V₀′
  → W ∣ γ ⊢²
      ((V₀ ↓ seal Xᴸ R) ↑ unseal Xᴸ R)
      ⊑ ((V₀′ ↓ seal Xᴿ R′) ↑ unseal Xᴿ R′) ∶ q
  → ((V₀ ↓ seal Xᴸ R) ↑ unseal Xᴸ R) —→[ keep ] V₀
  → ((V₀′ ↓ seal Xᴿ R′) ↑ unseal Xᴿ R′) —→[ keep ] V₀′
  → W ∣ γ ⊢² V₀ ⊑ V₀′ ∶ q


SourceOnlyConcealRevealPeelᵀ : Set
SourceOnlyConcealRevealPeelᵀ =
  ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {V₀ : Term Δᴸ} {V₀′ : Term Δᴿ}
    {Xᴸ : TyVar Δᴸ} {R : Ty Δᴸ} {R′ : Ty Δᴿ}
    {q : R ⊑ᵂ⟨ W ⟩ R′}
  → Value V₀
  → Value V₀′
  → TargetOpenedByConcealReveal V₀′ R′
  → W ∣ γ ⊢²
      ((V₀ ↓ seal Xᴸ R) ↑ unseal Xᴸ R)
      ⊑ V₀′ ∶ q
  → ((V₀ ↓ seal Xᴸ R) ↑ unseal Xᴸ R) —→[ keep ] V₀
  → W ∣ γ ⊢² V₀ ⊑ V₀′ ∶ q


record SimConversionFramesSuppliedParkedᵀ : Set₁ where
  field
    source-reveal-frame :
      ∀ {Δᴸ Δᴿ Δ Δᴸ′} {W Wᵖ : World Δᴸ Δᴿ Δ}
        {γᵖ : CtxImp Wᵖ}
        {M : Term Δᴸ} {M′ : Term Δᴿ} {N : Term Δᴸ′}
        {A A′ : Ty Δᴸ} {B : Ty Δᴿ} {Xᴸ?}
        {p : A ⊑ᵂ⟨ Wᵖ ⟩ B}
        {q : A′ ⊑ᵂ⟨ W ⟩ B}
        {c : Conv↑ Δᴸ A A′}
        {χᴸ : StoreChange Δᴸ Δᴸ′}
      → ParkedWorld W
      → ParkedWorld Wᵖ
      → ImpEnvMono W Wᵖ
      → RebaseAtᴸ W Wᵖ Xᴸ?
      → SameCtx {W = W} {W′ = Wᵖ} [] γᵖ
      → CTI2.sourceStoreʷ W CTI2.⊢↑[ Xᴸ? ] c
      → Wᵖ ∣ γᵖ ⊢² M ⊑ M′ ∶ p
      → W ∣ [] ⊢² M ↑ c ⊑ M′ ∶ q
      → M ↑ c —→[ χᴸ ] N
      → Σ[ Δᴿ′ ∈ TyCtx ]
        Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
        Σ[ N′ ∈ Term Δᴿ′ ] Σ[ Δ′ ∈ TyCtx ]
        Σ[ W′ ∈ World Δᴸ′ Δᴿ′ Δ′ ]
        Σ[ r ∈ applyTy χᴸ A′ ⊑ᵂ⟨ W′ ⟩ applyTys χsᴿ B ]
          (M′ —↠[ χsᴿ ] N′) ×
          ParkedEvolve (χᴸ ∷ˢ []ˢ) χsᴿ W W′ ×
          (W′ ∣ [] ⊢² N ⊑ N′ ∶ r)

    target-reveal-frame :
      ∀ {Δᴸ Δᴿ Δ Δᴸ′} {W Wᵖ : World Δᴸ Δᴿ Δ}
        {γᵖ : CtxImp Wᵖ}
        {M : Term Δᴸ} {M′ : Term Δᴿ} {N : Term Δᴸ′}
        {A : Ty Δᴸ} {B B′ : Ty Δᴿ} {Xᴿ?}
        {p : A ⊑ᵂ⟨ Wᵖ ⟩ B}
        {q : A ⊑ᵂ⟨ W ⟩ B′}
        {c′ : Conv↑ Δᴿ B B′}
        {χᴸ : StoreChange Δᴸ Δᴸ′}
      → ParkedWorld W
      → ParkedWorld Wᵖ
      → ImpEnvMono W Wᵖ
      → RebaseAtᴿ W Wᵖ Xᴿ?
      → SameCtx {W = W} {W′ = Wᵖ} [] γᵖ
      → CTI2.targetStoreʷ W CTI2.⊢↑[ Xᴿ? ] c′
      → Wᵖ ∣ γᵖ ⊢² M ⊑ M′ ∶ p
      → W ∣ [] ⊢² M ⊑ M′ ↑ c′ ∶ q
      → M —→[ χᴸ ] N
      → Σ[ Δᴿ′ ∈ TyCtx ]
        Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
        Σ[ N′ ∈ Term Δᴿ′ ] Σ[ Δ′ ∈ TyCtx ]
        Σ[ W′ ∈ World Δᴸ′ Δᴿ′ Δ′ ]
        Σ[ r ∈ applyTy χᴸ A ⊑ᵂ⟨ W′ ⟩ applyTys χsᴿ B′ ]
          (M′ ↑ c′ —↠[ χsᴿ ] N′) ×
          ParkedEvolve (χᴸ ∷ˢ []ˢ) χsᴿ W W′ ×
          (W′ ∣ [] ⊢² N ⊑ N′ ∶ r)

    source-conceal-frame :
      ∀ {Δᴸ Δᴿ Δ Δᴸ′} {W Wᵖ : World Δᴸ Δᴿ Δ}
        {γᵖ : CtxImp Wᵖ}
        {M : Term Δᴸ} {M′ : Term Δᴿ} {N : Term Δᴸ′}
        {A A′ : Ty Δᴸ} {B : Ty Δᴿ} {Xᴸ? Xᴿ?}
        {p : A ⊑ᵂ⟨ Wᵖ ⟩ B}
        {q : A′ ⊑ᵂ⟨ W ⟩ B}
        {c : Conv↓ Δᴸ A A′}
        {χᴸ : StoreChange Δᴸ Δᴸ′}
      → ParkedWorld W
      → ParkedWorld Wᵖ
      → CTI2.SourceConcealPartnerOK Wᵖ M c Xᴿ? M′
      → ImpEnvMono W Wᵖ
      → TagRebaseAtᴸ Wᵖ W Xᴸ? Xᴿ?
      → SameCtx {W = W} {W′ = Wᵖ} [] γᵖ
      → CTI2.sourceStoreʷ W CTI2.⊢↓[ Xᴸ? ] c
      → Wᵖ ∣ γᵖ ⊢² M ⊑ M′ ∶ p
      → W ∣ [] ⊢² M ↓ c ⊑ M′ ∶ q
      → M ↓ c —→[ χᴸ ] N
      → Σ[ Δᴿ′ ∈ TyCtx ]
        Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
        Σ[ N′ ∈ Term Δᴿ′ ] Σ[ Δ′ ∈ TyCtx ]
        Σ[ W′ ∈ World Δᴸ′ Δᴿ′ Δ′ ]
        Σ[ r ∈ applyTy χᴸ A′ ⊑ᵂ⟨ W′ ⟩ applyTys χsᴿ B ]
          (M′ —↠[ χsᴿ ] N′) ×
          ParkedEvolve (χᴸ ∷ˢ []ˢ) χsᴿ W W′ ×
          (W′ ∣ [] ⊢² N ⊑ N′ ∶ r)

    target-conceal-frame :
      ∀ {Δᴸ Δᴿ Δ Δᴸ′} {W Wᵖ : World Δᴸ Δᴿ Δ}
        {γᵖ : CtxImp Wᵖ}
        {M : Term Δᴸ} {M′ : Term Δᴿ} {N : Term Δᴸ′}
        {A : Ty Δᴸ} {B B′ : Ty Δᴿ} {Xᴿ?}
        {p : A ⊑ᵂ⟨ Wᵖ ⟩ B}
        {q : A ⊑ᵂ⟨ W ⟩ B′}
        {c′ : Conv↓ Δᴿ B B′}
        {χᴸ : StoreChange Δᴸ Δᴸ′}
      → ParkedWorld W
      → ParkedWorld Wᵖ
      → ImpEnvMono W Wᵖ
      → RebaseAtᴿ Wᵖ W Xᴿ?
      → SameCtx {W = W} {W′ = Wᵖ} [] γᵖ
      → CTI2.targetStoreʷ W CTI2.⊢↓[ Xᴿ? ] c′
      → Wᵖ ∣ γᵖ ⊢² M ⊑ M′ ∶ p
      → W ∣ [] ⊢² M ⊑ M′ ↓ c′ ∶ q
      → M —→[ χᴸ ] N
      → Σ[ Δᴿ′ ∈ TyCtx ]
        Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
        Σ[ N′ ∈ Term Δᴿ′ ] Σ[ Δ′ ∈ TyCtx ]
        Σ[ W′ ∈ World Δᴸ′ Δᴿ′ Δ′ ]
        Σ[ r ∈ applyTy χᴸ A ⊑ᵂ⟨ W′ ⟩ applyTys χsᴿ B′ ]
          (M′ ↓ c′ —↠[ χsᴿ ] N′) ×
          ParkedEvolve (χᴸ ∷ˢ []ˢ) χsᴿ W W′ ×
          (W′ ∣ [] ⊢² N ⊑ N′ ∶ r)


record SuppliedBoundaryStack {Δᴸ Δᴿ Δ}
    (kind : CatchupBoundaryKind)
    (Xᴸ? : Maybe (TyVar Δᴸ)) (Xᴿ? : Maybe (TyVar Δᴿ))
    (W Wᵖ : World Δᴸ Δᴿ Δ) : Set₁ where
  field
    boundary-outer-parked : ParkedWorld W
    boundary-premise-parked : ParkedWorld Wᵖ
    boundary-certificate : CatchupBoundary kind Xᴸ? Xᴿ? W Wᵖ


record SimConversionFramesBoundaryStackᵀ : Set₁ where
  field
    source-reveal-frame :
      ∀ {Δᴸ Δᴿ Δ Δᴸ′} {W Wᵖ : World Δᴸ Δᴿ Δ}
        {γᵖ : CtxImp Wᵖ}
        {M : Term Δᴸ} {M′ : Term Δᴿ} {N : Term Δᴸ′}
        {A A′ : Ty Δᴸ} {B : Ty Δᴿ} {Xᴸ? Xᴿ?}
        {p : A ⊑ᵂ⟨ Wᵖ ⟩ B}
        {q : A′ ⊑ᵂ⟨ W ⟩ B}
        {c : Conv↑ Δᴸ A A′}
        {χᴸ : StoreChange Δᴸ Δᴸ′}
      → SuppliedBoundaryStack source-reveal-boundary Xᴸ? Xᴿ? W Wᵖ
      → ImpEnvMono W Wᵖ
      → RebaseAtᴸ W Wᵖ Xᴸ?
      → SameCtx {W = W} {W′ = Wᵖ} [] γᵖ
      → CTI2.sourceStoreʷ W CTI2.⊢↑[ Xᴸ? ] c
      → Wᵖ ∣ γᵖ ⊢² M ⊑ M′ ∶ p
      → W ∣ [] ⊢² M ↑ c ⊑ M′ ∶ q
      → M ↑ c —→[ χᴸ ] N
      → Σ[ Δᴿ′ ∈ TyCtx ]
        Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
        Σ[ N′ ∈ Term Δᴿ′ ] Σ[ Δ′ ∈ TyCtx ]
        Σ[ W′ ∈ World Δᴸ′ Δᴿ′ Δ′ ]
        Σ[ r ∈ applyTy χᴸ A′ ⊑ᵂ⟨ W′ ⟩ applyTys χsᴿ B ]
          (M′ —↠[ χsᴿ ] N′) ×
          ParkedEvolve (χᴸ ∷ˢ []ˢ) χsᴿ W W′ ×
          (W′ ∣ [] ⊢² N ⊑ N′ ∶ r)

    target-reveal-frame :
      ∀ {Δᴸ Δᴿ Δ Δᴸ′} {W Wᵖ : World Δᴸ Δᴿ Δ}
        {γᵖ : CtxImp Wᵖ}
        {M : Term Δᴸ} {M′ : Term Δᴿ} {N : Term Δᴸ′}
        {A : Ty Δᴸ} {B B′ : Ty Δᴿ} {Xᴸ? Xᴿ?}
        {p : A ⊑ᵂ⟨ Wᵖ ⟩ B}
        {q : A ⊑ᵂ⟨ W ⟩ B′}
        {c′ : Conv↑ Δᴿ B B′}
        {χᴸ : StoreChange Δᴸ Δᴸ′}
      → SuppliedBoundaryStack target-reveal-boundary Xᴸ? Xᴿ? W Wᵖ
      → ImpEnvMono W Wᵖ
      → RebaseAtᴿ W Wᵖ Xᴿ?
      → SameCtx {W = W} {W′ = Wᵖ} [] γᵖ
      → CTI2.targetStoreʷ W CTI2.⊢↑[ Xᴿ? ] c′
      → Wᵖ ∣ γᵖ ⊢² M ⊑ M′ ∶ p
      → W ∣ [] ⊢² M ⊑ M′ ↑ c′ ∶ q
      → M —→[ χᴸ ] N
      → Σ[ Δᴿ′ ∈ TyCtx ]
        Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
        Σ[ N′ ∈ Term Δᴿ′ ] Σ[ Δ′ ∈ TyCtx ]
        Σ[ W′ ∈ World Δᴸ′ Δᴿ′ Δ′ ]
        Σ[ r ∈ applyTy χᴸ A ⊑ᵂ⟨ W′ ⟩ applyTys χsᴿ B′ ]
          (M′ ↑ c′ —↠[ χsᴿ ] N′) ×
          ParkedEvolve (χᴸ ∷ˢ []ˢ) χsᴿ W W′ ×
          (W′ ∣ [] ⊢² N ⊑ N′ ∶ r)

    source-conceal-frame :
      ∀ {Δᴸ Δᴿ Δ Δᴸ′} {W Wᵖ : World Δᴸ Δᴿ Δ}
        {γᵖ : CtxImp Wᵖ}
        {M : Term Δᴸ} {M′ : Term Δᴿ} {N : Term Δᴸ′}
        {A A′ : Ty Δᴸ} {B : Ty Δᴿ} {Xᴸ? Xᴿ?}
        {p : A ⊑ᵂ⟨ Wᵖ ⟩ B}
        {q : A′ ⊑ᵂ⟨ W ⟩ B}
        {c : Conv↓ Δᴸ A A′}
        {χᴸ : StoreChange Δᴸ Δᴸ′}
      → SuppliedBoundaryStack source-conceal-boundary Xᴸ? Xᴿ? W Wᵖ
      → CTI2.SourceConcealPartnerOK Wᵖ M c Xᴿ? M′
      → ImpEnvMono W Wᵖ
      → TagRebaseAtᴸ Wᵖ W Xᴸ? Xᴿ?
      → SameCtx {W = W} {W′ = Wᵖ} [] γᵖ
      → CTI2.sourceStoreʷ W CTI2.⊢↓[ Xᴸ? ] c
      → Wᵖ ∣ γᵖ ⊢² M ⊑ M′ ∶ p
      → W ∣ [] ⊢² M ↓ c ⊑ M′ ∶ q
      → M ↓ c —→[ χᴸ ] N
      → Σ[ Δᴿ′ ∈ TyCtx ]
        Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
        Σ[ N′ ∈ Term Δᴿ′ ] Σ[ Δ′ ∈ TyCtx ]
        Σ[ W′ ∈ World Δᴸ′ Δᴿ′ Δ′ ]
        Σ[ r ∈ applyTy χᴸ A′ ⊑ᵂ⟨ W′ ⟩ applyTys χsᴿ B ]
          (M′ —↠[ χsᴿ ] N′) ×
          ParkedEvolve (χᴸ ∷ˢ []ˢ) χsᴿ W W′ ×
          (W′ ∣ [] ⊢² N ⊑ N′ ∶ r)

    target-conceal-frame :
      ∀ {Δᴸ Δᴿ Δ Δᴸ′} {W Wᵖ : World Δᴸ Δᴿ Δ}
        {γᵖ : CtxImp Wᵖ}
        {M : Term Δᴸ} {M′ : Term Δᴿ} {N : Term Δᴸ′}
        {A : Ty Δᴸ} {B B′ : Ty Δᴿ} {Xᴸ? Xᴿ?}
        {p : A ⊑ᵂ⟨ Wᵖ ⟩ B}
        {q : A ⊑ᵂ⟨ W ⟩ B′}
        {c′ : Conv↓ Δᴿ B B′}
        {χᴸ : StoreChange Δᴸ Δᴸ′}
      → SuppliedBoundaryStack target-conceal-boundary Xᴸ? Xᴿ? W Wᵖ
      → ImpEnvMono W Wᵖ
      → RebaseAtᴿ Wᵖ W Xᴿ?
      → SameCtx {W = W} {W′ = Wᵖ} [] γᵖ
      → CTI2.targetStoreʷ W CTI2.⊢↓[ Xᴿ? ] c′
      → Wᵖ ∣ γᵖ ⊢² M ⊑ M′ ∶ p
      → W ∣ [] ⊢² M ⊑ M′ ↓ c′ ∶ q
      → M —→[ χᴸ ] N
      → Σ[ Δᴿ′ ∈ TyCtx ]
        Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
        Σ[ N′ ∈ Term Δᴿ′ ] Σ[ Δ′ ∈ TyCtx ]
        Σ[ W′ ∈ World Δᴸ′ Δᴿ′ Δ′ ]
        Σ[ r ∈ applyTy χᴸ A ⊑ᵂ⟨ W′ ⟩ applyTys χsᴿ B′ ]
          (M′ ↓ c′ —↠[ χsᴿ ] N′) ×
          ParkedEvolve (χᴸ ∷ˢ []ˢ) χsᴿ W W′ ×
          (W′ ∣ [] ⊢² N ⊑ N′ ∶ r)


record TargetRevealKeepOutcomeContinuationsᵀ : Set₁ where
  field
    paired-conceal-reveal :
      PairedConcealRevealPeelᵀ
    source-opened-conceal-reveal :
      SourceOnlyConcealRevealPeelᵀ


record TargetConcealKeepOutcomeContinuationsᵀ : Set₁ where
  field
    paired-id-conceal :
      ∀ {Δᴸ Δᴿ Δ}
        {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
        {V₀ : Term Δᴸ} {V₀′ : Term Δᴿ}
        {A : Ty Δᴸ} {B : Ty Δᴿ}
        {q : A ⊑ᵂ⟨ W ⟩ B}
      → Value V₀
      → Value V₀′
      → W ∣ γ ⊢²
          (V₀ ↓ Conversion.id↓ A)
          ⊑ (V₀′ ↓ Conversion.id↓ B) ∶ q
      → (V₀ ↓ Conversion.id↓ A) —→[ keep ] V₀
      → (V₀′ ↓ Conversion.id↓ B) —→[ keep ] V₀′
      → W ∣ γ ⊢² V₀ ⊑ V₀′ ∶ q

    source-opened-id-conceal :
      ∀ {Δᴸ Δᴿ Δ}
        {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
        {V₀ : Term Δᴸ} {V₀′ : Term Δᴿ}
        {A : Ty Δᴸ} {B : Ty Δᴿ}
        {q : A ⊑ᵂ⟨ W ⟩ B}
      → Value V₀
      → Value V₀′
      → W ∣ γ ⊢² (V₀ ↓ Conversion.id↓ A) ⊑ V₀′ ∶ q
      → (V₀ ↓ Conversion.id↓ A) —→[ keep ] V₀
      → W ∣ γ ⊢² V₀ ⊑ V₀′ ∶ q


record RestatedDispatcherKeepOutcomesᵀ : Set₁ where
  field
    target-reveal-outcomes : TargetRevealKeepOutcomeContinuationsᵀ
    target-conceal-outcomes : TargetConcealKeepOutcomeContinuationsᵀ

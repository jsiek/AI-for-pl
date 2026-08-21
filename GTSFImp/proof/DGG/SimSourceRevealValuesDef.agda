module proof.DGG.SimSourceRevealValuesDef where

-- File Charter:
--   * States source-only reveal closing after the target body has caught up
--     to a related value.
--   * Takes the catchup result as evidence; it does not perform catchup.
--   * Contains no source-reveal value proof.

open import Data.List using ([])
open import Data.Maybe using (Maybe)
open import Data.Product using (_×_; Σ-syntax)

open import Types using (Ty; TyCtx; TyVar)
open import Conversion using (Conv↑)
open import CastTerms using (Term; Value; _↑_)
open import Reduction using
  ( StoreChange
  ; StoreChanges
  ; applyTy
  ; applyTys
  ; _—→[_]_
  ; _—↠[_]_
  ) renaming ([] to []ˢ; _∷_ to _∷ˢ_)
import Conversion as Conv
import proof.DGG.CastTermImprecision as CTI2
import proof.DGG.CtxImp as CTX
open import proof.DGG.Parked.ParkedWorldDef
  using (ParkedWorld; ParkedEvolve)
open import proof.DGG.CatchupToMorePreciseDef
  using
    ( ValueCatchupResult
    ; source-reveal-boundary
    ; targetPivotᴸ
    )
open import proof.DGG.ConversionPivotAlignment
  using (generatorBoundaryPivot; revealGeneratorPosition)
open CTX using
  (World;
   ImpEnvMono;
   RebaseAtᴸ;
   sourceStoreʷ;
   _⊑ᵂ⟨_⟩_)
open CTI2 using (_∣_⊢²_⊑_∶_)


SimSourceRevealValuesᵀ : Set₁
SimSourceRevealValuesᵀ =
  ∀ {Δᴸ Δᴿ Δ Δᴸ′} {W Wᵖ : World Δᴸ Δᴿ Δ}
    {χᴸ : StoreChange Δᴸ Δᴸ′}
    {V : Term Δᴸ} {M′ : Term Δᴿ} {N : Term Δᴸ′}
    {A A′ Rᴸ : Ty Δᴸ} {B : Ty Δᴿ}
    {Xᴸ : TyVar Δᴸ}
    {c : Conv↑ Δᴸ A A′}
    {p : A ⊑ᵂ⟨ Wᵖ ⟩ B}
  → ParkedWorld W
  → (mono : ImpEnvMono W Wᵖ)
  → (c⊢ : sourceStoreʷ W Conv.⊢↑[ Xᴸ ⦂ Rᴸ ] c)
  → (rebase : RebaseAtᴸ W Wᵖ
      (generatorBoundaryPivot Xᴸ (revealGeneratorPosition c⊢)))
  → Wᵖ ∣ [] ⊢² V ⊑ M′ ∶ p
  → (q : A′ ⊑ᵂ⟨ W ⟩ B)
  → W ∣ [] ⊢² V ↑ c ⊑ M′ ∶ q
  → Value V
  → V ↑ c —→[ χᴸ ] N
  → ValueCatchupResult
      {W = W} {Wᵖ = Wᵖ} {kind = source-reveal-boundary}
      {Xᴸ? = generatorBoundaryPivot Xᴸ
        (revealGeneratorPosition c⊢)}
      {Xᴿ? = targetPivotᴸ rebase}
      {V = V} {M′ = M′} {A = A} {B = B}
  → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ N′ ∈ Term Δᴿ′ ] Σ[ Δ′ ∈ TyCtx ]
    Σ[ W′ ∈ World Δᴸ′ Δᴿ′ Δ′ ]
    Σ[ r ∈ applyTy χᴸ A′ ⊑ᵂ⟨ W′ ⟩ applyTys χsᴿ B ]
      (M′ —↠[ χsᴿ ] N′) ×
      ParkedEvolve (χᴸ ∷ˢ []ˢ) χsᴿ W W′ ×
      (W′ ∣ [] ⊢² N ⊑ N′ ∶ r)

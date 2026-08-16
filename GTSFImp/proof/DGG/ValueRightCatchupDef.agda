module proof.DGG.ValueRightCatchupDef where

-- File Charter:
--   * States closed target catch-up from a related more precise source value.
--   * The less precise target reaches a related value; unlike source catch-up,
--     this direction has no blame alternative.
--   * Contains no catch-up proof.

open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax)

open import Types using (Ty; TyCtx)
open import CastTerms using (Term; Value)
open import Reduction using (StoreChanges; applyTys; _—↠[_]_)
import proof.DGG.CastTermImprecision2 as CTI2
open import proof.DGG.Parked.ParkedWorldDef
  using (ParkedWorld; ParkedEvolve)
open CTI2 using (World; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_)


ValueRightCatchupᵀ : Set
ValueRightCatchupᵀ =
  ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {V : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ B}
  → ParkedWorld W
  → W ∣ [] ⊢² V ⊑ M′ ∶ p
  → Value V
  → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ V′ ∈ Term Δᴿ′ ] Σ[ Δ′ ∈ TyCtx ]
    Σ[ W′ ∈ World Δᴸ Δᴿ′ Δ′ ]
    Σ[ q ∈ A ⊑ᵂ⟨ W′ ⟩ applyTys χsᴿ B ]
      (M′ —↠[ χsᴿ ] V′) × Value V′ ×
      ParkedEvolve Reduction.[] χsᴿ W W′ ×
      (W′ ∣ [] ⊢² V ⊑ V′ ∶ q)

module proof.DGG.CatchupDef where

-- File Charter:
--   * States closed source catch-up when the less precise right term is
--     already a value.
--   * The more precise source reaches either a related value or blame while
--     the target remains fixed.
--   * Contains no catch-up proof.

open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax)
open import Data.Sum using (_⊎_)

open import Types using (Ty; TyCtx)
open import CastTerms using (Term; Value; blame)
open import Reduction using (StoreChanges; applyTys; _—↠[_]_)
import proof.DGG.CastTermImprecision2 as CTI2
open import proof.DGG.Parked.ParkedWorldDef
  using (ParkedWorld; ParkedEvolve)
open CTI2 using (World; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_)


Catchupᵀ : Set
Catchupᵀ =
  ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {M : Term Δᴸ} {V′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ B}
  → ParkedWorld W
  → W ∣ [] ⊢² M ⊑ V′ ∶ p
  → Value V′
  → (Σ[ Δᴸ′ ∈ TyCtx ] Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
      Σ[ V ∈ Term Δᴸ′ ] Σ[ Δ′ ∈ TyCtx ]
      Σ[ W′ ∈ World Δᴸ′ Δᴿ Δ′ ]
      Σ[ q ∈ applyTys χsᴸ A ⊑ᵂ⟨ W′ ⟩ B ]
        (M —↠[ χsᴸ ] V) × Value V ×
        ParkedEvolve χsᴸ Reduction.[] W W′ ×
        (W′ ∣ [] ⊢² V ⊑ V′ ∶ q))
    ⊎ (Σ[ Δᴸ′ ∈ TyCtx ] Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
        Σ[ Δ′ ∈ TyCtx ] Σ[ W′ ∈ World Δᴸ′ Δᴿ Δ′ ]
          (M —↠[ χsᴸ ] blame) ×
          ParkedEvolve χsᴸ Reduction.[] W W′)

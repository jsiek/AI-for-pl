module proof.DGG.TargetBlameCatchupDef where

-- File Charter:
--   * States closed source catch-up when the less precise target is blame.
--   * Supplies the source-blame observation needed by the divergence half of
--     the top-level dynamic gradual guarantee.
--   * Contains no catch-up proof.

open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax)

open import Types using (Ty; TyCtx)
open import CastTerms using (Term; blame)
open import Reduction using (StoreChanges; _—↠[_]_)
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.CtxImp as CTX
open import proof.DGG.Parked.ParkedWorldDef
  using (ParkedWorld; ParkedEvolve)
open CTX using
  (World;
   _⊑ᵂ⟨_⟩_)
open CTI2 using (_∣_⊢²_⊑_∶_)


TargetBlameCatchupᵀ : Set
TargetBlameCatchupᵀ =
  ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {M : Term Δᴸ} {A : Ty Δᴸ} {B : Ty Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ B}
  → ParkedWorld W
  → W ∣ [] ⊢² M ⊑ blame ∶ p
  → Σ[ Δᴸ′ ∈ TyCtx ] Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
    Σ[ Δ′ ∈ TyCtx ] Σ[ W′ ∈ World Δᴸ′ Δᴿ Δ′ ]
      (M —↠[ χsᴸ ] blame) ×
      ParkedEvolve χsᴸ Reduction.[] W W′

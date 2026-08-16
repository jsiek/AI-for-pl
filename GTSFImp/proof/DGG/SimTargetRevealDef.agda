module proof.DGG.SimTargetRevealDef where

-- File Charter:
--   * States simulation beneath a target reveal wrapper.
--   * Hides all rebased-premise reasoning and returns the complete Simᵀ
--     square for the source step.
--   * Contains no target-reveal simulation proof.

open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax)

open import Types using (Ty; TyCtx)
open import Conversion using (Conv↑)
open import CastTerms using (Term; _↑_)
open import Reduction using
  ( StoreChange
  ; StoreChanges
  ; applyTy
  ; applyTys
  ; _—→[_]_
  ; _—↠[_]_
  ) renaming ([] to []ˢ; _∷_ to _∷ˢ_)
import proof.DGG.CastTermImprecision2 as CTI2
open import proof.DGG.Parked.ParkedWorldDef
  using (ParkedWorld; ParkedEvolve)
open CTI2 using (World; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_)


SimTargetRevealᵀ : Set
SimTargetRevealᵀ =
  ∀ {Δᴸ Δᴿ Δ Δᴸ′} {W : World Δᴸ Δᴿ Δ}
    {M : Term Δᴸ} {M′ : Term Δᴿ} {N : Term Δᴸ′}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ}
    {c′ : Conv↑ Δᴿ B B′} {q : A ⊑ᵂ⟨ W ⟩ B′}
    {χᴸ : StoreChange Δᴸ Δᴸ′}
  → ParkedWorld W
  → W ∣ [] ⊢² M ⊑ M′ ↑ c′ ∶ q
  → M —→[ χᴸ ] N
  → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ N′ ∈ Term Δᴿ′ ] Σ[ Δ′ ∈ TyCtx ]
    Σ[ W′ ∈ World Δᴸ′ Δᴿ′ Δ′ ]
    Σ[ r ∈ applyTy χᴸ A ⊑ᵂ⟨ W′ ⟩ applyTys χsᴿ B′ ]
      (M′ ↑ c′ —↠[ χsᴿ ] N′) ×
      ParkedEvolve (χᴸ ∷ˢ []ˢ) χsᴿ W W′ ×
      (W′ ∣ [] ⊢² N ⊑ N′ ∶ r)

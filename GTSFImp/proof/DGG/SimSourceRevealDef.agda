module proof.DGG.SimSourceRevealDef where

-- File Charter:
--   * States simulation for a source reveal wrapper.
--   * Hides all rebased-premise reasoning and returns the complete Simᵀ
--     square for the wrapper step.
--   * Contains no source-reveal simulation proof.

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


SimSourceRevealᵀ : Set
SimSourceRevealᵀ =
  ∀ {Δᴸ Δᴿ Δ Δᴸ′} {W : World Δᴸ Δᴿ Δ}
    {M : Term Δᴸ} {M′ : Term Δᴿ} {N : Term Δᴸ′}
    {A A′ : Ty Δᴸ} {B : Ty Δᴿ}
    {c : Conv↑ Δᴸ A A′} {q : A′ ⊑ᵂ⟨ W ⟩ B}
    {χᴸ : StoreChange Δᴸ Δᴸ′}
  → ParkedWorld W
  → W ∣ [] ⊢² M ↑ c ⊑ M′ ∶ q
  → M ↑ c —→[ χᴸ ] N
  → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ N′ ∈ Term Δᴿ′ ] Σ[ Δ′ ∈ TyCtx ]
    Σ[ W′ ∈ World Δᴸ′ Δᴿ′ Δ′ ]
    Σ[ r ∈ applyTy χᴸ A′ ⊑ᵂ⟨ W′ ⟩ applyTys χsᴿ B ]
      (M′ —↠[ χsᴿ ] N′) ×
      ParkedEvolve (χᴸ ∷ˢ []ˢ) χsᴿ W W′ ×
      (W′ ∣ [] ⊢² N ⊑ N′ ∶ r)

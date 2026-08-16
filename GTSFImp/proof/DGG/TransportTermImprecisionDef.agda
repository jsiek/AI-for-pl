module proof.DGG.TransportTermImprecisionDef where

-- File Charter:
--   * States transport of closed term imprecision through parked evolution.
--   * Applies the source and target store-change traces to both terms and
--     reuses the canonical parked transport of the related result type.
--   * Contains no term-imprecision transport proof.

open import Data.List using ([])

open import Types using (Ty)
open import CastTerms using (Term)
open import Reduction using (StoreChanges; applyTerms)
import proof.DGG.CastTermImprecision2 as CTI2
open import proof.DGG.Parked.ParkedWorldDef using (ParkedEvolve)
open import proof.DGG.Parked.ParkedWorldLemma using (transport⊑ᴾ)
open CTI2 using (World; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_)


TransportTermImprecisionᴾᵀ : Set
TransportTermImprecisionᴾᵀ =
  ∀ {Δᴸ Δᴸ′ Δᴿ Δᴿ′ Δ Δ′}
    {χsᴸ : StoreChanges Δᴸ Δᴸ′}
    {χsᴿ : StoreChanges Δᴿ Δᴿ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ′ Δᴿ′ Δ′}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ B}
  → (evol : ParkedEvolve χsᴸ χsᴿ W W′)
  → W ∣ [] ⊢² M ⊑ M′ ∶ p
  → W′ ∣ [] ⊢² applyTerms χsᴸ M ⊑ applyTerms χsᴿ M′
      ∶ transport⊑ᴾ evol p

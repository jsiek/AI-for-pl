module proof.DGG.SimBetaDef where

-- File Charter:
--   * States simulation of source beta reduction after a related lambda is
--     applied to a related source value.
--   * Packages all target catch-up, parked-world evolution, and the final
--     substituted term relation behind one higher-order interface.
--   * Contains no beta-simulation proof.

open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax)

open import Types using (Ty; TyCtx; _⇒_)
open import Imprecision using (⇒⊑⇒)
open import CastTerms using (Term; Value; ƛ_; _·_; _[_])
open import Reduction using
  ( StoreChanges
  ; applyTys
  ; keep
  ; _—↠[_]_
  ) renaming ([] to []ˢ; _∷_ to _∷ˢ_)
import proof.DGG.CastTermImprecision2 as CTI2
open import proof.DGG.Parked.ParkedWorldDef
  using (ParkedWorld; ParkedEvolve)
open CTI2 using (World; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_)


SimBetaᵀ : Set
SimBetaᵀ =
  ∀ {Δᴸ Δᴿ Δ} {world : World Δᴸ Δᴿ Δ}
    {M V : Term Δᴸ} {L′ M′ : Term Δᴿ}
    {A B : Ty Δᴸ} {A′ B′ : Ty Δᴿ}
    {pA : A ⊑ᵂ⟨ world ⟩ A′} {pB : B ⊑ᵂ⟨ world ⟩ B′}
  → ParkedWorld world
  → world ∣ [] ⊢² ƛ M ⊑ L′ ∶ ⇒⊑⇒ pA pB
  → world ∣ [] ⊢² V ⊑ M′ ∶ pA
  → Value V
  → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ N′ ∈ Term Δᴿ′ ] Σ[ Δ′ ∈ TyCtx ]
    Σ[ world′ ∈ World Δᴸ Δᴿ′ Δ′ ]
    Σ[ q ∈ B ⊑ᵂ⟨ world′ ⟩ applyTys χsᴿ B′ ]
      (L′ · M′ —↠[ χsᴿ ] N′) ×
      ParkedEvolve (keep ∷ˢ []ˢ) χsᴿ world world′ ×
      (world′ ∣ [] ⊢² M [ V ] ⊑ N′ ∶ q)

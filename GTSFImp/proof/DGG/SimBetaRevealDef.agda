module proof.DGG.SimBetaRevealDef where

-- File Charter:
--   * States simulation of source function-reveal beta reduction.
--   * Packages target catch-up, reduction, parked-world evolution, and the
--     final distributed argument/result conversions behind one interface.
--   * Contains no beta-reveal simulation proof.

open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax)

open import Types using (Ty; TyCtx; _⇒_)
open import Conversion using (Conv↑; Conv↓; _↦↑_)
open import Imprecision using (⇒⊑⇒)
open import CastTerms using (Term; Value; _·_; _↑_; _↓_)
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


SimBetaRevealᵀ : Set
SimBetaRevealᵀ =
  ∀ {Δᴸ Δᴿ Δ} {world : World Δᴸ Δᴿ Δ}
    {V M : Term Δᴸ} {L′ M′ : Term Δᴿ}
    {A A′ B B′ A₀ B₀ : Ty Δᴸ} {C D : Ty Δᴿ}
    {c : Conv↓ Δᴸ A′ A} {d : Conv↑ Δᴸ B B′}
    {pA : A₀ ⊑ᵂ⟨ world ⟩ C}
    {pB : B₀ ⊑ᵂ⟨ world ⟩ D}
  → ParkedWorld world
  → world ∣ [] ⊢² V ↑ (c ↦↑ d) ⊑ L′ ∶ ⇒⊑⇒ pA pB
  → world ∣ [] ⊢² M ⊑ M′ ∶ pA
  → Value V
  → Value M
  → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ N′ ∈ Term Δᴿ′ ] Σ[ Δ′ ∈ TyCtx ]
    Σ[ world′ ∈ World Δᴸ Δᴿ′ Δ′ ]
    Σ[ q ∈ B₀ ⊑ᵂ⟨ world′ ⟩ applyTys χsᴿ D ]
      (L′ · M′ —↠[ χsᴿ ] N′) ×
      ParkedEvolve (keep ∷ˢ []ˢ) χsᴿ world world′ ×
      (world′ ∣ [] ⊢² (V · (M ↓ c)) ↑ d ⊑ N′ ∶ q)

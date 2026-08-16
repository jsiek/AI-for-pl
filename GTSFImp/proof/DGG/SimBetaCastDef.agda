module proof.DGG.SimBetaCastDef where

-- File Charter:
--   * States simulation of source function-cast beta reduction.
--   * Packages target catch-up, target reduction, parked-world evolution,
--     and the final casted application relation behind one interface.
--   * Contains no beta-cast simulation proof.

open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax)

open import Types using (Ty; TyCtx; _⇒_)
open import Consistency using (Env∼; flipᵐ; _⊢_∼_; _↦_)
open import Imprecision using (⇒⊑⇒)
open import CastTerms using (Term; Value; _·_; _⟨_⟩)
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


SimBetaCastᵀ : Set
SimBetaCastᵀ =
  ∀ {Δᴸ Δᴿ Δ} {world : World Δᴸ Δᴿ Δ}
    {V W : Term Δᴸ} {L′ M′ : Term Δᴿ}
    {μ : Env∼ Δᴸ} {A A′ B B′ A₀ B₀ : Ty Δᴸ}
    {C D : Ty Δᴿ}
    {c : flipᵐ μ ⊢ A′ ∼ A} {d : μ ⊢ B ∼ B′}
    {pA : A₀ ⊑ᵂ⟨ world ⟩ C}
    {pB : B₀ ⊑ᵂ⟨ world ⟩ D}
  → ParkedWorld world
  → world ∣ [] ⊢² V ⟨ c ↦ d ⟩ ⊑ L′ ∶ ⇒⊑⇒ pA pB
  → world ∣ [] ⊢² W ⊑ M′ ∶ pA
  → Value V
  → Value W
  → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ N′ ∈ Term Δᴿ′ ] Σ[ Δ′ ∈ TyCtx ]
    Σ[ world′ ∈ World Δᴸ Δᴿ′ Δ′ ]
    Σ[ q ∈ B₀ ⊑ᵂ⟨ world′ ⟩ applyTys χsᴿ D ]
      (L′ · M′ —↠[ χsᴿ ] N′) ×
      ParkedEvolve (keep ∷ˢ []ˢ) χsᴿ world world′ ×
      (world′ ∣ [] ⊢² (V · (W ⟨ c ⟩)) ⟨ d ⟩ ⊑ N′ ∶ q)

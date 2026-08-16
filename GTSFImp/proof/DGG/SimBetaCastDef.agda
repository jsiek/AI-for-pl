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
  ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {V X : Term Δᴸ} {F′ X′ : Term Δᴿ}
    {μ : Env∼ Δᴸ} {A A′ B B′ A₀ B₀ : Ty Δᴸ}
    {C D : Ty Δᴿ}
    {c : flipᵐ μ ⊢ A′ ∼ A} {d : μ ⊢ B ∼ B′}
    {pA : A₀ ⊑ᵂ⟨ W ⟩ C} {pB : B₀ ⊑ᵂ⟨ W ⟩ D}
  → ParkedWorld W
  → W ∣ [] ⊢² V ⟨ c ↦ d ⟩ ⊑ F′ ∶ ⇒⊑⇒ pA pB
  → W ∣ [] ⊢² X ⊑ X′ ∶ pA
  → Value V
  → Value X
  → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ R′ ∈ Term Δᴿ′ ] Σ[ Δ′ ∈ TyCtx ]
    Σ[ W′ ∈ World Δᴸ Δᴿ′ Δ′ ]
    Σ[ q ∈ B₀ ⊑ᵂ⟨ W′ ⟩ applyTys χsᴿ D ]
      (F′ · X′ —↠[ χsᴿ ] R′) ×
      ParkedEvolve (keep ∷ˢ []ˢ) χsᴿ W W′ ×
      (W′ ∣ [] ⊢² (V · (X ⟨ c ⟩)) ⟨ d ⟩ ⊑ R′ ∶ q)

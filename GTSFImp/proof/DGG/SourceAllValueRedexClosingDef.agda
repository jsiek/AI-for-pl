module proof.DGG.SourceAllValueRedexClosingDef where

-- File Charter:
--   * States the source-only post-catchup universal-redex closing surface.
--   * The target endpoint is already a value and does not take a matching
--     target type-application step.
--   * The conclusion packages source-only parked evolution and the
--     instantiated source body relation against the same target value.
--   * Contains no proof scripts or adapters to the top-down Sim interface.

open import Data.List using ([])
import Data.Nat as Nat
open import Data.Product using (_×_; Σ-syntax)

open import Types using (Ty; TyCtx; ★; `∀; _[_]ᵗ)
open import CastTerms using (Term; Value; _⦂∀_[_])
open import Reduction using
  ( StoreChange
  ; applyTy
  ; _—→[_]_
  ) renaming ([] to []ˢ; _∷_ to _∷ˢ_)
import proof.DGG.CastTermImprecision2 as CTI2
open import proof.DGG.Parked.ParkedWorldDef
  using (ParkedWorld; ParkedEvolve)
open CTI2 using (World; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_)


SourceAllValueRedexClosingᵀ : Set
SourceAllValueRedexClosingᵀ =
  ∀ {Δᴸ Δᴿ Δ Δᴸ′} {world : World Δᴸ Δᴿ Δ}
    {χᴸ : StoreChange Δᴸ Δᴸ′}
    {V : Term Δᴸ} {V′ : Term Δᴿ} {N : Term Δᴸ′}
    {C : Ty (Nat.suc Δᴸ)} {A : Ty Δᴸ} {B : Ty Δᴿ}
    {p∀ : `∀ C ⊑ᵂ⟨ world ⟩ B}
  → ParkedWorld world
  → world ∣ [] ⊢² V ⊑ V′ ∶ p∀
  → (q : A ⊑ᵂ⟨ world ⟩ ★)
  → (r : C [ A ]ᵗ ⊑ᵂ⟨ world ⟩ B)
  → Value V
  → Value V′
  → V ⦂∀ C [ A ] —→[ χᴸ ] N
  → Σ[ Δ′ ∈ TyCtx ] Σ[ world′ ∈ World Δᴸ′ Δᴿ Δ′ ]
    Σ[ s ∈ applyTy χᴸ (C [ A ]ᵗ) ⊑ᵂ⟨ world′ ⟩ B ]
      ParkedEvolve (χᴸ ∷ˢ []ˢ) []ˢ world world′ ×
      (world′ ∣ [] ⊢² N ⊑ V′ ∶ s)

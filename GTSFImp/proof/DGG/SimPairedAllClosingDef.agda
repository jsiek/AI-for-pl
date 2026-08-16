module proof.DGG.SimPairedAllClosingDef where

-- File Charter:
--   * States simulation of a paired source/target type application when the
--     source head is a value and its type application takes a beta step.
--   * Packages target catch-up, target type-application reduction, and
--     parked-world evolution behind one source-rule-independent interface.
--   * Contains no paired universal-closing proof or rule-specific adapter.

open import Data.List using ([])
import Data.Nat as Nat
open import Data.Product using (_×_; Σ-syntax)

open import Types using (Ty; TyCtx; `∀; _[_]ᵗ)
open import CastTerms using (Term; Value; _⦂∀_[_])
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


SimPairedAllClosingᵀ : Set
SimPairedAllClosingᵀ =
  ∀ {Δᴸ Δᴿ Δ Δᴸ′} {world : World Δᴸ Δᴿ Δ}
    {χᴸ : StoreChange Δᴸ Δᴸ′}
    {V : Term Δᴸ} {M′ : Term Δᴿ} {N : Term Δᴸ′}
    {C : Ty (Nat.suc Δᴸ)} {A : Ty Δᴸ}
    {C′ : Ty (Nat.suc Δᴿ)} {A′ : Ty Δᴿ}
    {p∀ : `∀ C ⊑ᵂ⟨ world ⟩ `∀ C′}
  → ParkedWorld world
  → world ∣ [] ⊢² V ⊑ M′ ∶ p∀
  → (q : A ⊑ᵂ⟨ world ⟩ A′)
  → (r : C [ A ]ᵗ ⊑ᵂ⟨ world ⟩ C′ [ A′ ]ᵗ)
  → Value V
  → V ⦂∀ C [ A ] —→[ χᴸ ] N
  → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ N′ ∈ Term Δᴿ′ ] Σ[ Δ′ ∈ TyCtx ]
    Σ[ world′ ∈ World Δᴸ′ Δᴿ′ Δ′ ]
    Σ[ s ∈ applyTy χᴸ (C [ A ]ᵗ) ⊑ᵂ⟨ world′ ⟩
        applyTys χsᴿ (C′ [ A′ ]ᵗ) ]
      (M′ ⦂∀ C′ [ A′ ] —↠[ χsᴿ ] N′) ×
      ParkedEvolve (χᴸ ∷ˢ []ˢ) χsᴿ world world′ ×
      (world′ ∣ [] ⊢² N ⊑ N′ ∶ s)

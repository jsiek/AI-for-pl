module proof.DGG.PairedAllValueRedexClosingDef where

-- File Charter:
--   * States the paired post-catchup universal-redex closing surface.
--   * The target head is already a value and carries an `AllValueView`.
--   * The conclusion packages the target beta trace, parked evolution, and
--     instantiated source/target body relation.
--   * Contains no proof scripts or adapters to the top-down Sim interface.

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
open import proof.DGG.Inversion.SpineValueDef using (AllValueView)
open import proof.DGG.Parked.ParkedWorldDef
  using (ParkedWorld; ParkedEvolve)
open CTI2 using (World; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_)


PairedAllValueRedexClosingᵀ : Set
PairedAllValueRedexClosingᵀ =
  ∀ {Δᴸ Δᴿ Δ Δᴸ′} {world : World Δᴸ Δᴿ Δ}
    {χᴸ : StoreChange Δᴸ Δᴸ′}
    {V : Term Δᴸ} {V′ : Term Δᴿ} {N : Term Δᴸ′}
    {C : Ty (Nat.suc Δᴸ)} {A : Ty Δᴸ}
    {C′ : Ty (Nat.suc Δᴿ)} {A′ : Ty Δᴿ}
    {p∀ : `∀ C ⊑ᵂ⟨ world ⟩ `∀ C′}
  → ParkedWorld world
  → world ∣ [] ⊢² V ⊑ V′ ∶ p∀
  → (q : A ⊑ᵂ⟨ world ⟩ A′)
  → (r : C [ A ]ᵗ ⊑ᵂ⟨ world ⟩ C′ [ A′ ]ᵗ)
  → Value V
  → Value V′
  → AllValueView V′
  → V ⦂∀ C [ A ] —→[ χᴸ ] N
  → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ N′ ∈ Term Δᴿ′ ] Σ[ Δ′ ∈ TyCtx ]
    Σ[ world′ ∈ World Δᴸ′ Δᴿ′ Δ′ ]
    Σ[ s ∈ applyTy χᴸ (C [ A ]ᵗ) ⊑ᵂ⟨ world′ ⟩
        applyTys χsᴿ (C′ [ A′ ]ᵗ) ]
      (V′ ⦂∀ C′ [ A′ ] —↠[ χsᴿ ] N′) ×
      ParkedEvolve (χᴸ ∷ˢ []ˢ) χsᴿ world world′ ×
      (world′ ∣ [] ⊢² N ⊑ N′ ∶ s)

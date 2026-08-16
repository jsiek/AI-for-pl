module proof.DGG.SimSourceAllClosingDef where

-- File Charter:
--   * States source-universal closing against an arbitrary target term.
--   * Packages target catch-up and source-only world evolution for any
--     value-headed type-application step.
--   * Contains no source-universal closing proof or rule-specific adapter.

open import Data.List using ([])
import Data.Nat as Nat
open import Data.Product using (_×_; Σ-syntax)

open import Types using (Ty; TyCtx; ★; `∀; _[_]ᵗ)
open import CastTerms using (Term; Value; _⦂∀_[_])
open import Reduction using
  ( StoreChanges
  ; StoreChange
  ; applyTy
  ; applyTys
  ; _—→[_]_
  ; _—↠[_]_
  ) renaming ([] to []ˢ; _∷_ to _∷ˢ_)
import proof.DGG.CastTermImprecision2 as CTI2
open import proof.DGG.Parked.ParkedWorldDef
  using (ParkedWorld; ParkedEvolve)
open CTI2 using (World; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_)


SimSourceAllClosingᵀ : Set
SimSourceAllClosingᵀ =
  ∀ {Δᴸ Δᴿ Δ Δᴸ′} {world : World Δᴸ Δᴿ Δ}
    {χᴸ : StoreChange Δᴸ Δᴸ′}
    {V : Term Δᴸ} {M′ : Term Δᴿ} {N : Term Δᴸ′}
    {C : Ty (Nat.suc Δᴸ)} {A : Ty Δᴸ} {B : Ty Δᴿ}
    {p∀ : `∀ C ⊑ᵂ⟨ world ⟩ B}
  → ParkedWorld world
  → world ∣ [] ⊢² V ⊑ M′ ∶ p∀
  → (q : A ⊑ᵂ⟨ world ⟩ ★)
  → (r : C [ A ]ᵗ ⊑ᵂ⟨ world ⟩ B)
  → Value V
  → V ⦂∀ C [ A ] —→[ χᴸ ] N
  → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ N′ ∈ Term Δᴿ′ ] Σ[ Δ′ ∈ TyCtx ]
    Σ[ world′ ∈ World Δᴸ′ Δᴿ′ Δ′ ]
    Σ[ s ∈ applyTy χᴸ (C [ A ]ᵗ) ⊑ᵂ⟨ world′ ⟩
        applyTys χsᴿ B ]
      (M′ —↠[ χsᴿ ] N′) ×
      ParkedEvolve (χᴸ ∷ˢ []ˢ) χsᴿ world world′ ×
      (world′ ∣ [] ⊢² N ⊑ N′ ∶ s)

module proof.DGG.SimSourceCastValuesDef where

-- File Charter:
--   * States simulation of a source-only ordinary cast after its target body
--     has caught up to a related value.
--   * Keeps that target value and its store fixed while the source cast closes.
--   * Packages all value/value source-cast roots behind one interface.

open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax)

open import Types using (Ty; TyCtx)
open import Consistency using (Env∼; _⊢_∼_)
open import CastTerms using (Term; Value; _⟨_⟩)
open import Reduction using
  ( StoreChange
  ; applyTy
  ; _—→[_]_
  ) renaming ([] to []ˢ; _∷_ to _∷ˢ_)
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.CtxImp as CTX
open import proof.DGG.Parked.ParkedWorldDef
  using (ParkedWorld; ParkedEvolve)
open CTX using
  (World;
   _⊑ᵂ⟨_⟩_)
open CTI2 using (_∣_⊢²_⊑_∶_)


SimSourceCastValuesᵀ : Set
SimSourceCastValuesᵀ =
  ∀ {Δᴸ Δᴿ Δ Δᴸ′} {world : World Δᴸ Δᴿ Δ}
    {χᴸ : StoreChange Δᴸ Δᴸ′}
    {V : Term Δᴸ} {V′ : Term Δᴿ} {N : Term Δᴸ′}
    {A B : Ty Δᴸ} {C : Ty Δᴿ}
    {μ : Env∼ Δᴸ} {c : μ ⊢ A ∼ B}
    {p : A ⊑ᵂ⟨ world ⟩ C}
  → ParkedWorld world
  → world ∣ [] ⊢² V ⊑ V′ ∶ p
  → (q : B ⊑ᵂ⟨ world ⟩ C)
  → Value V
  → Value V′
  → V ⟨ c ⟩ —→[ χᴸ ] N
  → Σ[ Δ′ ∈ TyCtx ]
    Σ[ world′ ∈ World Δᴸ′ Δᴿ Δ′ ]
    Σ[ r ∈ applyTy χᴸ B ⊑ᵂ⟨ world′ ⟩ C ]
      ParkedEvolve (χᴸ ∷ˢ []ˢ) []ˢ world world′ ×
      (world′ ∣ [] ⊢² N ⊑ V′ ∶ r)

module proof.DGG.SimPairedCastValuesDef where

-- File Charter:
--   * States simulation of a paired ordinary cast after both cast bodies
--     have reached related values.
--   * Packages all value/value cast-root combinations behind one interface.
--   * Does not perform the initial target catch-up or split by cast rule.

open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax)

open import Types using (Ty; TyCtx)
open import Consistency using (Env∼; _⊢_∼_)
open import CastTerms using (Term; Value; _⟨_⟩)
open import Reduction using
  ( StoreChange
  ; StoreChanges
  ; applyTy
  ; applyTys
  ; _—→[_]_
  ; _—↠[_]_
  ) renaming ([] to []ˢ; _∷_ to _∷ˢ_)
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.CtxImp as CTX
open import proof.DGG.Parked.ParkedWorldDef
  using (ParkedWorld; ParkedEvolve)
open CTX using
  (World;
   _⊑ᵂ⟨_⟩_)
open CTI2 using (_∣_⊢²_⊑_∶_)


SimPairedCastValuesᵀ : Set
SimPairedCastValuesᵀ =
  ∀ {Δᴸ Δᴿ Δ Δᴸ′} {world : World Δᴸ Δᴿ Δ}
    {χᴸ : StoreChange Δᴸ Δᴸ′}
    {V : Term Δᴸ} {V′ : Term Δᴿ} {N : Term Δᴸ′}
    {A B : Ty Δᴸ} {A′ B′ : Ty Δᴿ}
    {μ : Env∼ Δᴸ} {μ′ : Env∼ Δᴿ}
    {c : μ ⊢ A ∼ B} {c′ : μ′ ⊢ A′ ∼ B′}
    {p : A ⊑ᵂ⟨ world ⟩ A′}
  → ParkedWorld world
  → world ∣ [] ⊢² V ⊑ V′ ∶ p
  → (q : B ⊑ᵂ⟨ world ⟩ B′)
  → Value V
  → Value V′
  → V ⟨ c ⟩ —→[ χᴸ ] N
  → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ N′ ∈ Term Δᴿ′ ] Σ[ Δ′ ∈ TyCtx ]
    Σ[ world′ ∈ World Δᴸ′ Δᴿ′ Δ′ ]
    Σ[ r ∈ applyTy χᴸ B ⊑ᵂ⟨ world′ ⟩ applyTys χsᴿ B′ ]
      (V′ ⟨ c′ ⟩ —↠[ χsᴿ ] N′) ×
      ParkedEvolve (χᴸ ∷ˢ []ˢ) χsᴿ world world′ ×
      (world′ ∣ [] ⊢² N ⊑ N′ ∶ r)

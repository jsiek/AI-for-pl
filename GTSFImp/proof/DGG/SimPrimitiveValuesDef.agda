module proof.DGG.SimPrimitiveValuesDef where

-- File Charter:
--   * States simulation of a primitive reduction after both target operands
--     have caught up to related values.
--   * Packages all value/value primitive delta squares behind one interface.
--   * Contains no primitive simulation proof or operand catch-up reasoning.

open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax)

open import Types using (TyCtx)
open import Primitives using
  (primArgTy; primResultTy; δ)
open import CastTerms using (Term; Value; $; _⊕[_]_)
open import Reduction using
  ( StoreChanges
  ; applyTys
  ; keep
  ; _—↠[_]_
  ) renaming ([] to []ˢ; _∷_ to _∷ˢ_)
import proof.DGG.CastTermImprecision as CTI2
import proof.DGG.CtxImp as CTX
open import proof.DGG.Parked.ParkedWorldDef
  using (ParkedWorld; ParkedEvolve)
open CTX using
  (World;
   _⊑ᵂ⟨_⟩_)
open CTI2 using (_∣_⊢²_⊑_∶_)


SimPrimitiveValuesᵀ : Set
SimPrimitiveValuesᵀ =
  ∀ {Δᴸ Δᴿ Δ} {world : World Δᴸ Δᴿ Δ}
    {op κ κ′ κ″} {V′ M′ : Term Δᴿ}
    {p q : primArgTy op ⊑ᵂ⟨ world ⟩ primArgTy op}
  → ParkedWorld world
  → world ∣ [] ⊢² $ κ ⊑ V′ ∶ p
  → world ∣ [] ⊢² $ κ′ ⊑ M′ ∶ q
  → (r : primResultTy op ⊑ᵂ⟨ world ⟩ primResultTy op)
  → Value V′
  → Value M′
  → δ op κ κ′ κ″
  → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ N′ ∈ Term Δᴿ′ ] Σ[ Δ′ ∈ TyCtx ]
    Σ[ world′ ∈ World Δᴸ Δᴿ′ Δ′ ]
    Σ[ s ∈ primResultTy op ⊑ᵂ⟨ world′ ⟩
        applyTys χsᴿ (primResultTy op) ]
      (V′ ⊕[ op ] M′ —↠[ χsᴿ ] N′) ×
      ParkedEvolve (keep ∷ˢ []ˢ) χsᴿ world world′ ×
      (world′ ∣ [] ⊢² $ κ″ ⊑ N′ ∶ s)

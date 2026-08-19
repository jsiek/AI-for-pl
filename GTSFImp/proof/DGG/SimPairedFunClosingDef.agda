module proof.DGG.SimPairedFunClosingDef where

-- File Charter:
--   * States simulation of a paired source/target application when both
--     source operands are values and the source application takes a beta
--     step.
--   * Packages target function and argument catch-up behind one
--     source-rule-independent interface.
--   * Contains no paired function-closing proof or rule-specific adapter.

open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax)

open import Types using (Ty; TyCtx)
open import CastTerms using (Term; Value; _·_)
open import Reduction using
  ( StoreChanges
  ; applyTys
  ; keep
  ; _—→[_]_
  ; _—↠[_]_
  ) renaming ([] to []ˢ; _∷_ to _∷ˢ_)
open import Imprecision using (⇒⊑⇒)
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.CtxImp as CTX
open import proof.DGG.Parked.ParkedWorldDef
  using (ParkedWorld; ParkedEvolve)
open CTX using
  (World;
   _⊑ᵂ⟨_⟩_)
open CTI2 using (_∣_⊢²_⊑_∶_)


SimPairedFunClosingᵀ : Set
SimPairedFunClosingᵀ =
  ∀ {Δᴸ Δᴿ Δ} {world : World Δᴸ Δᴿ Δ}
    {L M N : Term Δᴸ} {L′ M′ : Term Δᴿ}
    {A B : Ty Δᴸ} {A′ B′ : Ty Δᴿ}
    {pA : A ⊑ᵂ⟨ world ⟩ A′} {pB : B ⊑ᵂ⟨ world ⟩ B′}
  → ParkedWorld world
  → world ∣ [] ⊢² L ⊑ L′ ∶ ⇒⊑⇒ pA pB
  → world ∣ [] ⊢² M ⊑ M′ ∶ pA
  → Value L
  → Value M
  → L · M —→[ keep ] N
  → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ N′ ∈ Term Δᴿ′ ] Σ[ Δ′ ∈ TyCtx ]
    Σ[ world′ ∈ World Δᴸ Δᴿ′ Δ′ ]
    Σ[ q ∈ B ⊑ᵂ⟨ world′ ⟩ applyTys χsᴿ B′ ]
      (L′ · M′ —↠[ χsᴿ ] N′) ×
      ParkedEvolve (keep ∷ˢ []ˢ) χsᴿ world world′ ×
      (world′ ∣ [] ⊢² N ⊑ N′ ∶ q)

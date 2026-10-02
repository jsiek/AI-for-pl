module proof.DGG.TermSubstClosingDef where

-- File Charter:
--   * States the single-variable CTI2 term-substitution corollary needed by
--     paired function beta closing.
--   * The full D8a boundary-indexed substitution family is expected to prove
--     this surface in a separate proof module.
--   * Contains no proof script and no simulation adapter.

open import Data.List using (_∷_)
open import Data.Product using (Σ-syntax)

open import Types using (Ty)
open import CastTerms using (Term; _[_])
import proof.DGG.CastTermImprecision2 as CTI2
open CTI2 using
  ( World
  ; CtxImp
  ; ctx-imp
  ; _⊑ᵂ⟨_⟩_
  ; _∣_⊢²_⊑_∶_
  )


⊢²-single-substᵀ : Set
⊢²-single-substᵀ =
  ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W}
    {N M : Term Δᴸ} {N′ V : Term Δᴿ}
    {A B : Ty Δᴸ} {A′ B′ : Ty Δᴿ}
    {pA : A ⊑ᵂ⟨ W ⟩ A′}
    {pB : B ⊑ᵂ⟨ W ⟩ B′}
  → W ∣ ctx-imp A A′ pA ∷ γ ⊢² N ⊑ N′ ∶ pB
  → W ∣ γ ⊢² M ⊑ V ∶ pA
  → W ∣ γ ⊢² N [ M ] ⊑ N′ [ V ] ∶ pB

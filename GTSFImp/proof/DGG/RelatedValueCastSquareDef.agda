{-# OPTIONS --safe #-}

module proof.DGG.RelatedValueCastSquareDef where

-- File Charter:
--   * States the diagonal type-imprecision fact for a consistency square
--     whose upper endpoints contain related values.
--   * Isolates the genuine value/typing induction that rules out the empty
--     bottom-type corner of an otherwise valid consistency square.
--   * Contains no cast-reduction classifier or simulation result wrapper.

open import Types using (Ty)
open import Consistency using (Env∼; _⊢_∼_)
open import CastTerms using (Ctx; Δᵉ; Term; Value)
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.DGG.World


RelatedValueCastSquareᵀ : Set
RelatedValueCastSquareᵀ = ∀ {Γᴸ Γᴿ : Ctx}
    {γ : Γᴸ ⊑ᶜ Γᴿ}
    {V : Term (Δᵉ Γᴸ)} {V′ : Term (Δᵉ Γᴿ)}
    {A B : Ty (Δᵉ Γᴸ)} {A′ B′ : Ty (Δᵉ Γᴿ)}
    {μ : Env∼ (Δᵉ Γᴸ)} {μ′ : Env∼ (Δᵉ Γᴿ)}
    {c : μ ⊢ A ∼ B} {c′ : μ′ ⊢ A′ ∼ B′}
    {p : A ⊑ᵀ⟨ γ ⟩ A′}
  → γ ⊢² V ⊑ V′ ∶ p
  → Value V
  → Value V′
  → B ⊑ᵀ⟨ γ ⟩ B′
  → B ⊑ᵀ⟨ γ ⟩ A′

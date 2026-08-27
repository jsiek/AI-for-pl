{-# OPTIONS --safe #-}

module
  proof.DGG.Catchup.MorePrecisePairedTargetInstantiationInputSquareDef where

-- File Charter:
--   * States the type-imprecision square exposed when a source inert cast is
--     paired with a target instantiation cast.
--   * The input relation at the two cast sources and the output relation at
--     the two cast targets determine the source-input-to-target-output edge.
--   * This is the pre-induction obligation needed to run exposed target
--     instantiation catch-up and then replay the source inert cast.
--   * Contains no cast classifier, result record, or catch-up proof.

open import Relation.Binary.PropositionalEquality using (_≢_)
open import Data.Nat using (suc)

open import Types using (Ty; TyCtx; ★; `∀; ⇑ᵗ)
open import Consistency using (Env∼; _⊢_∼_; instᵐ)
open import CastTerms using (Ctx; Δᵉ; Inert)
open import proof.DGG.World using (_⊑ᶜ_; _⊑ᵀ⟨_⟩_)


MorePrecisePairedTargetInstantiationInputSquareᵀ : Set
MorePrecisePairedTargetInstantiationInputSquareᵀ = ∀ {Γᴸ Γᴿ : Ctx}
    {γ : Γᴸ ⊑ᶜ Γᴿ}
    {C A : Ty (Δᵉ Γᴸ)} {B : Ty (suc (Δᵉ Γᴿ))}
    {B′ : Ty (Δᵉ Γᴿ)} {νᴸ : Env∼ (Δᵉ Γᴸ)}
    {νᴿ : Env∼ (Δᵉ Γᴿ)}
    {cᴸ : νᴸ ⊢ C ∼ A} {cᴿ : instᵐ νᴿ ⊢ B ∼ ⇑ᵗ B′}
  → Inert cᴸ
  → B′ ≢ ★
  → C ⊑ᵀ⟨ γ ⟩ `∀ B
  → A ⊑ᵀ⟨ γ ⟩ B′
  → C ⊑ᵀ⟨ γ ⟩ B′

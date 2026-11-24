{-# OPTIONS --safe #-}

module
  proof.DGG.Catchup.MorePrecisePairedTargetGroundCastSquareDef where

-- File Charter:
--   * States the type-imprecision squares needed before recursively catching
--     up a target ground injection or projection paired specifically with a
--     source all or gen cast.
--   * Each all/gen injection formula turns the upper input relation, both
--     consistencies, and the source output-to-★ relation into the source
--     output-to-ground relation.
--   * Each all/gen projection formula turns the source input-to-★ relation,
--     both consistencies, and the lower output relation into the source
--     input-to-ground relation.
--   * Leaves the separate inductions through the all and gen consistency
--     cases outside target-cast catch-up.
--   * Contains no cast classifier, result record, or residual-family API.
--   * A formula quantified over every source inert cast would be false: for
--     source inj with ℕ ∼ ★ and a target identity at ℕ, its injection
--     conclusion would require ★ ⊑ ℕ.  The source-inj catch-up case instead
--     pairs the two generated tags directly.

import Data.Fin as Fin
open import Data.Nat using (suc)
open import Types using
  (Ty; Ground; NonStar; NonVar; _∈ᵗ_; ★; `∀; ⇑ᵗ)
open import Consistency using
  (Env∼; _⊢_∼_; extᵐ; genᵐ; gen_)
open import CastTerms using (Ctx; Δᵉ; GenSafe)
open import proof.DGG.World using (_⊑ᶜ_; _⊑ᵀ⟨_⟩_)


MorePrecisePairedTargetAllInjectionGroundSquareᵀ : Set
MorePrecisePairedTargetAllInjectionGroundSquareᵀ = ∀ {Γᴸ Γᴿ : Ctx}
    {γ : Γᴸ ⊑ᶜ Γᴿ}
    {C A : Ty (suc (Δᵉ Γᴸ))}
    {B G : Ty (Δᵉ Γᴿ)}
    {νᴸ : Env∼ (Δᵉ Γᴸ)} {νᴿ : Env∼ (Δᵉ Γᴿ)}
  → extᵐ νᴸ ⊢ C ∼ A
  → Ground G
  → NonStar B
  → νᴿ ⊢ B ∼ G
  → `∀ C ⊑ᵀ⟨ γ ⟩ B
  → `∀ A ⊑ᵀ⟨ γ ⟩ ★
  → `∀ A ⊑ᵀ⟨ γ ⟩ G


MorePrecisePairedTargetGenInjectionGroundSquareᵀ : Set
MorePrecisePairedTargetGenInjectionGroundSquareᵀ = ∀ {Γᴸ Γᴿ : Ctx}
    {γ : Γᴸ ⊑ᶜ Γᴿ}
    {C : Ty (Δᵉ Γᴸ)} {A : Ty (suc (Δᵉ Γᴸ))}
    {B G : Ty (Δᵉ Γᴿ)}
    {νᴸ : Env∼ (Δᵉ Γᴸ)} {νᴿ : Env∼ (Δᵉ Γᴿ)}
    {cᴸ : genᵐ νᴸ ⊢ ⇑ᵗ C ∼ A}
    ⦃ Anv : NonVar A ⦄ ⦃ zero∈A : Fin.zero ∈ᵗ A ⦄
  → GenSafe cᴸ
  → Ground G
  → NonStar B
  → νᴿ ⊢ B ∼ G
  → C ⊑ᵀ⟨ γ ⟩ B
  → `∀ A ⊑ᵀ⟨ γ ⟩ ★
  → `∀ A ⊑ᵀ⟨ γ ⟩ G


MorePrecisePairedTargetAllProjectionGroundSquareᵀ : Set
MorePrecisePairedTargetAllProjectionGroundSquareᵀ = ∀ {Γᴸ Γᴿ : Ctx}
    {γ : Γᴸ ⊑ᶜ Γᴿ}
    {C A : Ty (suc (Δᵉ Γᴸ))}
    {G B : Ty (Δᵉ Γᴿ)}
    {νᴸ : Env∼ (Δᵉ Γᴸ)} {νᴿ : Env∼ (Δᵉ Γᴿ)}
  → extᵐ νᴸ ⊢ C ∼ A
  → Ground G
  → NonStar B
  → νᴿ ⊢ G ∼ B
  → `∀ C ⊑ᵀ⟨ γ ⟩ ★
  → `∀ A ⊑ᵀ⟨ γ ⟩ B
  → `∀ C ⊑ᵀ⟨ γ ⟩ G


MorePrecisePairedTargetGenProjectionGroundSquareᵀ : Set
MorePrecisePairedTargetGenProjectionGroundSquareᵀ = ∀ {Γᴸ Γᴿ : Ctx}
    {γ : Γᴸ ⊑ᶜ Γᴿ}
    {C : Ty (Δᵉ Γᴸ)} {A : Ty (suc (Δᵉ Γᴸ))}
    {G B : Ty (Δᵉ Γᴿ)}
    {νᴸ : Env∼ (Δᵉ Γᴸ)} {νᴿ : Env∼ (Δᵉ Γᴿ)}
    {cᴸ : genᵐ νᴸ ⊢ ⇑ᵗ C ∼ A}
    ⦃ Anv : NonVar A ⦄ ⦃ zero∈A : Fin.zero ∈ᵗ A ⦄
  → GenSafe cᴸ
  → Ground G
  → NonStar B
  → νᴿ ⊢ G ∼ B
  → C ⊑ᵀ⟨ γ ⟩ ★
  → `∀ A ⊑ᵀ⟨ γ ⟩ B
  → C ⊑ᵀ⟨ γ ⟩ G

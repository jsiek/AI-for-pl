{-# OPTIONS --safe #-}

module proof.DGG.SourceGroundCastWitnessDef where

-- File Charter:
--   * States the two left-endpoint ground witnesses needed when a source
--     ordinary cast takes a ground or expansion step.
--   * Uses related source/target values to retain the world information that
--     is not present in the endpoint type obligations alone.
--   * Contains no source-cast simulation proof.

open import Types using (Ty; Ground; NonStar; ★)
open import Consistency using (Env∼; _⊢_∼_)
open import CastTerms using (Ctx; Δᵉ; Term; Value)
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.DGG.World


SourceGroundInjectionWitnessᵀ : Set
SourceGroundInjectionWitnessᵀ =
  ∀ {Γᴸ Γᴿ : Ctx} {γ : Γᴸ ⊑ᶜ Γᴿ}
    {V : Term (Δᵉ Γᴸ)} {V′ : Term (Δᵉ Γᴿ)}
    {A G : Ty (Δᵉ Γᴸ)} {C : Ty (Δᵉ Γᴿ)}
    {μ : Env∼ (Δᵉ Γᴸ)} {c : μ ⊢ A ∼ G}
    {Gᵍ : Ground G} {Ans : NonStar A}
    {p : A ⊑ᵀ⟨ γ ⟩ C}
  → γ ⊢² V ⊑ V′ ∶ p
  → Value V
  → Value V′
  → ★ ⊑ᵀ⟨ γ ⟩ C
  → G ⊑ᵀ⟨ γ ⟩ C


SourceGroundProjectionWitnessᵀ : Set
SourceGroundProjectionWitnessᵀ =
  ∀ {Γᴸ Γᴿ : Ctx} {γ : Γᴸ ⊑ᶜ Γᴿ}
    {V : Term (Δᵉ Γᴸ)} {V′ : Term (Δᵉ Γᴿ)}
    {G B : Ty (Δᵉ Γᴸ)} {C : Ty (Δᵉ Γᴿ)}
    {μ : Env∼ (Δᵉ Γᴸ)} {c : μ ⊢ G ∼ B}
    {Gᵍ : Ground G} {Bns : NonStar B}
    {p : ★ ⊑ᵀ⟨ γ ⟩ C}
  → γ ⊢² V ⊑ V′ ∶ p
  → Value V
  → Value V′
  → B ⊑ᵀ⟨ γ ⟩ C
  → G ⊑ᵀ⟨ γ ⟩ C

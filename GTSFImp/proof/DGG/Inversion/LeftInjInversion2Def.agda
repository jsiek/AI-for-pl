{-# OPTIONS --safe #-}

module proof.DGG.Inversion.LeftInjInversion2Def where

-- File Charter:
--   * States source generated-tag inversion for related spine values.
--   * Removes a source ground injection when the requested obligation exposes
--     that ground type directly.
--   * Contains no inversion proof.

open import Types using (Ty; Ground; NonStar; ★)
open import Consistency using (Env∼; _⊢_∼_; _⊢_∼★; _!)
open import CastTerms using (Ctx; Δᵉ; Term; Value; _⟨_⟩)
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.DGG.Inversion.SpineValueDef using (SpineValue)
open import proof.DGG.World


LeftInjInversion² : Set
LeftInjInversion² =
  ∀ {Γᴸ Γᴿ : Ctx} {γ : Γᴸ ⊑ᶜ Γᴿ}
    {M : Term (Δᵉ Γᴸ)} {N : Term (Δᵉ Γᴿ)}
    {H : Ty (Δᵉ Γᴸ)} {B : Ty (Δᵉ Γᴿ)}
    {μ : Env∼ (Δᵉ Γᴸ)}
    {gH : Ground H} {H∼★ : μ ⊢ H ∼★} {Hns : NonStar H}
    {cH : μ ⊢ H ∼ H}
    {p : ★ ⊑ᵀ⟨ γ ⟩ B}
  → SpineValue M
  → Value N
  → γ ⊢² M ⟨ _! ⦃ gH ⦄ ⦃ H∼★ ⦄ cH ⦃ Hns ⦄ ⟩ ⊑ N ∶ p
  → (q : H ⊑ᵀ⟨ γ ⟩ B)
  → γ ⊢² M ⊑ N ∶ q
